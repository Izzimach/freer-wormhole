
--
-- A basic freer monad. Based on various haskell libraries including freer-simple and
-- the paper "Freer Monads, More Extensible Effects" by Oleg Kiselyov and Hiromi Ishii
--

-- The Freer monad doesn't contain actual executable code, but instead
-- stores either a result value (Pure) or an effect plus continuation (Impure).
--

import Lean
import FreerWormhole.Wormhole

-- The basic Effect type holds a type of the possible operations/commands (usually a sum type)
-- and the appropriate return type(s) for each possible operation.
structure Effect : Type 2 where
   (op : Type 1)
   (ret : op → Type)

namespace Effect

inductive OU (effs : List Effect) : Type → Type 2 where
    | Node {eff : Effect} (ix : Fin effs.length) (h : effs[ix] = eff) (c : eff.op) : OU effs (eff.ret c)

-- peels off a single Effect type `eff` from this OU. If this OU is an effect `eff` it return Sum.inr with the 
-- op and proof that the return type of OU `x` is the correct type. If this OU is not an effect `eff` it returns
-- Sum.inl with an OU that has one less effect in it's effect list.
def decompOU {eff : Effect} {effs : List Effect} (ou : OU (eff :: effs) x) : Sum (OU effs x) (PSigma (fun (c : eff.op) => eff.ret c = x)) :=
    match ou with
    | .Node ⟨Nat.zero,l⟩ h c => Sum.inr <| show _ by rename_i eff2
                                                     let z : eff = eff2 := h
                                                     rw [z]
                                                     exact PSigma.mk c rfl
    | .Node ⟨Nat.succ n,l⟩ h c => have h1 : List.length (eff :: effs) = Nat.succ (List.length effs) := by simp
                                  have h2 : n < List.length effs := by apply Nat.lt_of_succ_lt_succ; rw [←h1]; exact l
                                  let ix2 : Fin effs.length := ⟨n,h2⟩
                                  Sum.inl <| show OU effs _ by rename_i eff2
                                                               -- rfl really doing some work here
                                                               have h4 : (eff :: effs)[Fin.mk (Nat.succ n) l] = effs[Fin.mk n h2] := by rfl
                                                               have h3 : effs[ix2]                            = eff2              := by simp; rw [←h4]; exact h
                                                               exact OU.Node ix2 h3 c

def weakenOU {eff : Effect} {effs : List Effect} : OU effs x → OU (eff :: effs) x
    | OU.Node ix h c => show OU (eff :: effs) _ by rename_i eff2
                                                   let ix2 := Fin.succ ix
                                                   have h2 : (eff :: effs)[ix2] = effs[ix] := rfl
                                                   have h3 : (eff :: effs)[ix2] = eff2     := by rw [h2]; exact h
                                                   exact @OU.Node (eff :: effs) eff2 ix2 h3 c


-- in essence this finds the index `ix` that points to where
-- `e` is in the list of effects `effs`, along with a proof
-- that `ix` points to the right place
class HasEffect (e : Effect) (effs : List Effect) where
    ixOf : PSigma (fun (ix : Fin effs.length) => effs[ix] = e)


instance : HasEffect e (e :: effs) where
    ixOf := PSigma.mk ⟨0,by simp; apply Nat.zero_lt_succ⟩ (by rfl)

instance [HasEffect e effs] : HasEffect e (z :: effs) where
    ixOf := let ⟨ix0, h0⟩ := @HasEffect.ixOf e effs _
            let ix1 : Fin (List.length (z :: effs)) := Fin.succ ix0
            have h4 : (z :: effs)[ix1] = effs[ix0] := by rfl
            PSigma.mk ix1 (by simp; rw [h4]; exact h0)

def inject {e : Effect} {effs : List Effect} [HasEffect e effs] (c : e.op) : OU effs (e.ret c) :=
    let ix := HasEffect.ixOf
    OU.Node ix.fst ix.snd c


-- A generic "run this effect" instance for monads. Built on top of HasEffect and HasHEffect.
-- This is so you can write one command for an effect (for instance get/put of
-- state) using send and have it work with both EffM and HEffM.
class SupportsEffect (e : Effect) (m : Type → Type 2) where
    send : (c : e.op) → m (e.ret c)

end Effect


inductive EffM (effs : List Effect) : Type → Type 2 where
    | Pure : a → EffM effs a
    | Impure : {x : Type} → Effect.OU effs x → (x → EffM effs a) → EffM effs a

namespace EffM

open Effect

instance [HasEffect e effs] : SupportsEffect e (EffM effs) where
    send := fun (c : e.op) => @EffM.Impure effs (e.ret c) _ (inject c) .Pure

-- Sometimes you have a monad with some effects but you need to pass it into a function
-- with additional effects you don't care about (see the Catch/Throw higher-order effect for instance).
def weaken {g : Effect} {effs : List Effect} : EffM effs a → EffM (g :: effs) a
    | .Pure a => .Pure a
    | .Impure ou next => .Impure (weakenOU ou) (fun x => weaken (next x))

def effMap {a b : Type} (f : a → b) (w : EffM effs a) : EffM effs b :=
    match w with
    | .Pure a => .Pure (f a)
    | .Impure gx next => .Impure gx (fun x => effMap f (next x))

instance : Functor (EffM effs) :=
    { map := effMap }

def EffAlg (effs : List Effect) (a : Type) := {x : Type} → (OU effs x) → (x → a) → a

-- EffAlg for a Type 1 result. We avoid "Type u" declarations since it complicates
-- a lot of the type inference.
def EffAlg1 (effs : List Effect) (a : Type 1) := {x : Type} → (OU effs x) → (x → a) → a
def EffAlg2 (effs : List Effect) (a : Type 2) := {x : Type} → (OU effs x) → (x → a) → a

def effCata {a : Type} (alg : EffAlg effs a) (w : EffM effs a) : a :=
    match w with
    | .Pure a => a
    | .Impure gx next => alg gx (fun x => effCata alg (next x))


/-
-- Bind for EffM just wraps in a continuation.
-/
def bindEff {a b : Type} (m : EffM effs a) (f : a → EffM effs b) : EffM effs b :=
    -- alternate implementation of bind using a fold, similar to the "Hefty Algebras" paper
    --@foldOver a (EffM effs b) effs f .Impure m
    match m with
    | .Pure a => f a
    | .Impure gx next => EffM.Impure gx (fun z => bindEff (next z) f)

def pureEff {α : Type} (a : α) : EffM effs α := EffM.Pure a



-- Handler is the handler for a specific effect: ret is for Pure constructors
-- and handle is for impure constructors. There is an 'inp' type so that the handler monad can
-- take inputs (a state monad would take input `s` for example). You can make input Unit to mean no input.
--  - a is the type returned from a Pure
--  - b is the monad result type. It may be that a=b but not always.
structure Handler (a : Type) (b : Type) (e : Effect) (effs : List Effect) (inp : Type) where
   (ret : a → inp → EffM effs b)
   (handle : EffAlg2 (e :: effs) (inp → EffM effs b))


-- Interpret a EffM monad. You must provide an "interpreter" which takes commands of type c
-- and produces monads of the final type n.  This runs the interpreter on a command
-- in the Impure constructor and combines it with the next chunk of the EffM monad
-- by using a definition of bind for the final monad n.
def handleEffect {a b : Type} {e : Effect} {effs : List Effect} {inp : Type} 
    (handler : Handler a b e effs inp) (m : EffM (e :: effs) a) : inp → EffM effs b :=
    match m with
    | .Pure a => handler.ret a
    | .Impure gx next => handler.handle gx (fun x => handleEffect handler (next x))


-- After handling all effects, you'll have a EffM [] a left over, use
-- runEff at the end to extract the result.
-- example : runEff <| h2 <| h1 m

def runEffect : EffM [] a → a
    | .Pure x => x
    -- shouldn't ever have an Impure constructed
    --| .Impure ou next => match ou with | .Leaf c => Fin.elim0 (ULift.down c)


end EffM

instance : Monad (EffM effs) where
    pure := EffM.pureEff
    bind := EffM.bindEff

instance : Pure (EffM effs) where
    pure := EffM.pureEff

instance : Bind (EffM effs) where
    bind := EffM.bindEff
