
import FreerWormhole.Effects.EffM

--
-- higher-order effects
--

structure HEffect : Type 2 where
    (cmd : Type 1)
    (fork : cmd  → Effect)
    (retH : cmd → Type)

namespace HEffect

open Effect EffM

-- Choose one HEffect from a list of them.
inductive HOU (heffs : List HEffect) : (ret : Type) → Effect → Type 2 where
    | Node : (ix : Fin heffs.length) → (h : heffs[ix] = heff) → (c : heff.cmd) → HOU heffs (heff.retH c) (heff.fork c) 

def decompHOU {heff : HEffect} {heffs : List HEffect} (hou : HOU (heff :: heffs) r x) : Sum (HOU heffs r x) (PSigma (fun (c : heff.cmd) => heff.retH c = r ∧ heff.fork c = x)) :=
    match hou with
    | .Node ⟨Nat.zero,l⟩ h c => let c' := show _ by rename_i heff2
                                                    let z : heff = heff2 := h
                                                    rw [z]
                                                    exact PSigma.mk c (And.intro rfl rfl)
                                Sum.inr c'
    | .Node ⟨Nat.succ n,l⟩ h c => have h1 : List.length (heff :: heffs) = Nat.succ (List.length heffs) := by simp
                                  have h2 : n < List.length heffs := by apply Nat.lt_of_succ_lt_succ; rw [←h1]; exact l
                                  let ix2 : Fin heffs.length := ⟨n,h2⟩
                                  Sum.inl <| show HOU heffs _ _ by
                                        rename_i heff2
                                        -- rfl really doing some work here
                                        have h4 : (heff :: heffs)[Fin.mk (Nat.succ n) l] = heffs[Fin.mk n h2] := by rfl
                                        have h3 : heffs[ix2]                             = heff2              := by simp; rw [←h4]; exact h
                                        exact HOU.Node ix2 h3 c

def weakenHOU {heff : HEffect} {heffs : List HEffect} : HOU heffs r x → HOU (heff :: heffs) r x
    | HOU.Node ix h c => show HOU (heff :: heffs) _ _ by
        rename_i heff2
        let ix2 := Fin.succ ix
        have h2 : (heff :: heffs)[ix2] = heffs[ix] := rfl
        have h3 : (heff :: heffs)[ix2] = heff2     := by rw [h2]; exact h
        exact @HOU.Node (heff :: heffs) heff2 ix2 h3 c


-- in essence this finds the index `ix` that points to where
-- `e` is in the list of effects `effs`, along with a proof
-- that `ix` points to the right place
class HasHEffect (heff : HEffect) (heffs : List HEffect) where
    ixOf : PSigma (fun (ix : Fin heffs.length) => heffs[ix] = heff)


instance : HasHEffect heff (heff :: heffs) where
    ixOf := PSigma.mk ⟨0,by simp; apply Nat.zero_lt_succ⟩ (by rfl)

instance [HasHEffect heff heffs] : HasHEffect heff (z :: heffs) where
    ixOf := let ⟨ix0, h0⟩ := @HasHEffect.ixOf heff heffs _
            let ix1 : Fin (List.length (z :: heffs)) := Fin.succ ix0
            have h4 : (z :: heffs)[ix1] = heffs[ix0] := by rfl
            PSigma.mk ix1 (by simp; rw [h4]; exact h0)

def inject {heff : HEffect} {heffs : List HEffect} [HasHEffect heff heffs] (c : heff.cmd) : HOU heffs (heff.retH c) (heff.fork c) :=
    let ix := HasHEffect.ixOf
    HOU.Node ix.fst ix.snd c

end HEffect

inductive HEffM : List HEffect → Type → Type 2 where
    | Pure {a : Type} : a → HEffM h a
    | Impure {a x : Type} {e : Effect} {h : List HEffect} : HEffect.HOU h x e → ((c : e.op) → HEffM h (e.ret c)) → (x → HEffM h a) → HEffM h a


namespace HEffM

open Effect EffM
open HEffect

def hPure (val : a) : HEffM h a := .Pure val

def hBind (m : HEffM h a) (f : a → HEffM h b) : HEffM h b :=
    match m with
    | .Pure a => f a
    | .Impure ou psi next => .Impure ou psi (fun x => hBind (next x) f)

instance : Monad (HEffM heffs) where
    pure := hPure
    bind := hBind


def hLift {heff : HEffect} {heffs : List HEffect} [HasHEffect heff heffs] 
      (c : heff.cmd)
      (hfork : (x : Effect.op (HEffect.fork heff c)) → HEffM heffs (Effect.ret (HEffect.fork heff c) x))
      : HEffM heffs (heff.retH c) :=
    HEffM.Impure (@HEffect.inject heff heffs _ c) hfork (fun z => HEffM.Pure z)

-- A version of `SupportsEffect` for HEffects
class SupportsHEffect (heff : HEffect) (m : Type → Type 2) where
    hSend : (c : heff.cmd) → (hfork : (x : Effect.op (HEffect.fork heff c)) → m (Effect.ret (HEffect.fork heff c) x)) → m (heff.retH c)

instance [HasHEffect heff heffs] : SupportsHEffect heff (HEffM heffs) where
    hSend := fun c hf => @hLift heff heffs _ c hf


-- an algebra for HEffM h a
def algH (heffs : List HEffect) (f : Type → Type 2) : Type 2 :=
    {x : Type} → {a : Type} → {e : Effect} → (c : HOU heffs x e) → ((s : e.op) → f ((e.ret s))) → (x → f a) → f a

def cataH {heffs : List HEffect} {a : Type} {f : Type → Type 2} (pf : {x : Type} → x → f x) (alg : algH heffs f) (t : HEffM heffs a) : f a :=
    match t with
    | HEffM.Pure x => pf x
    | HEffM.Impure ou psi next => alg ou (fun x => cataH pf alg (psi x)) (fun x => cataH pf alg (next x))


def Elaboration (heffs : List HEffect) (effs : List Effect) : Type 2 := algH heffs (EffM effs)

def elaborate (e : Elaboration heffs eff) (h : HEffM heffs a) : EffM eff a := cataH EffM.Pure e h

-- An Elaboration transforms a whole list of HEffects into a Freer of effects.
-- In contrast, an Elab1 does a single elaboration on a single HEffect.
-- You can use this to build up a full Elaboration by chaining several Elab1 terms.
def Elab1 (heff : HEffect) (heffs : List HEffect) (effs : List Effect) : Type 2 :=
    Elaboration heffs effs → Elaboration (heff :: heffs) effs


-- Elaborations are usually specified as cons-ing an HEffect onto an already-established list of HEffects.
-- To terminate this list of HEffect we use the NilEffect, which elaborates into an 
def NilEffect : Effect :=
    {
        -- we use Fin 0 as a stand-in for bottom
        op := ULift <| Fin 0,
        ret := fun _ => ULift <| Fin 0
    }

def NilHandler : Handler a a NilEffect effs Unit :=
    {
        ret := fun a _ => .Pure a,
        handle := fun ou next s =>
            match Effect.decompOU ou with
            | Sum.inr ⟨z,_⟩ => Fin.elim0 z.down
            | Sum.inl ou' => EffM.Impure ou' (fun x => next x ())
    }

def hLifted (eff : Effect) : HEffect := 
    {
        cmd := eff.op,
        fork := fun _ => NilEffect,
        retH := eff.ret
    }

-- send works with both EffM and HEffM
instance [HasHEffect (hLifted eff) heffs] : SupportsEffect eff (HEffM heffs) where
    send := fun (c : eff.op) => @HEffM.Impure _ (eff.ret c) NilEffect heffs (@HEffect.inject (hLifted eff) heffs _ c) (fun f0 => Fin.elim0 (ULift.down f0)) hPure



def elabEff (eff : Effect) [HasEffect eff effs] : Elab1 (hLifted eff) heffs effs :=
    fun elab0 => 
        fun op phi next =>
            match decompHOU op with
            | Sum.inr ⟨c,h⟩ => show _ by
                rename_i x a b
                let c' : eff.op := c
                let h' : ret eff c' = x := by rw [←h.left]; unfold retH; unfold hLifted; simp
                exact EffM.Impure (Effect.inject c') (show _ by rw [h']; exact next)
            | Sum.inl hou' => elab0 hou' phi next

-- When you use elabEff it works like List.cons, prepending an elaboration onto a list of elaborations.
-- At the end you need elabLast, which is sort of a List.nil for elaboration lists.
def elabLast (eff : Effect) [HasEffect eff effs] : Elaboration [hLifted eff] effs :=
    fun op phi next =>
        match decompHOU op with
        | Sum.inr ⟨c,h⟩ => show _ by
            rename_i x a b
            let c' : eff.op := c
            let h' : ret eff c' = x := by rw [←h.left]; unfold retH; unfold hLifted; simp
            exact EffM.Impure (Effect.inject c') (show _ by rw [h']; exact next)

-- a higher-order effect that should not be able to be constructed, used to terminate
-- Heff elaboration
def elabNil : Elaboration [hLifted NilEffect] [] :=
    fun op _ _ => match decompHOU op with | Sum.inr ⟨c,_⟩ => Fin.elim0 (ULift.down c)


end HEffM
