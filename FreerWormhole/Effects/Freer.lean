--
-- A basic freer monad. Based on various haskell libraries including freer-simple and
-- the paper "Freer Monads, More Extensible Effects" by Oleg Kiselyov and Hiromi Ishii
--

-- The Freer monad doesn't contain actual executable code, but instead
-- stores either a result value (Pure) or an effect plus continuation (Impure).
--

-- The basic Effect type holds a type of the possible operations/commands (usually a sum type)
-- and the appropriate return type(s) for each possible operation.
structure Effect.{u} : Type (u+1) where
   (op : Type u)
   (ret : op → Type u)

namespace Effect

-- The "Open Union" contains one operation from a list of possible effects,
-- determined at run time. This means we have to peel off .Node constructors, similar
-- to walking a list data type.
inductive OU : List Effect.{u} → Type u → Type (u+1) where
    | Leaf {eff : Effect.{u}} {effs : List Effect.{u}} : (c : eff.op) → OU (eff :: effs) (eff.ret c)
    | Node {eff : Effect} {effs : List Effect} : OU effs x → OU (eff :: effs) x


-- This is similar to Haseffect.project below, but instead of returning an (Option e.op) it
-- returns either an e.op or an OU with the relevant effect removed. Used when
-- running the handler for a specific effect.
def decompOU {e : Effect} {effs : List Effect} (ou : OU (e :: effs) x) : Sum (OU effs x) (e.op) :=
    match ou with
    | .Leaf x => Sum.inr x
    | .Node ou' => Sum.inl ou'                



class HasEffect (e : Effect) (effs : List Effect) where
    inject : (c : e.op) → OU effs (e.ret c)
    project : OU effs a → Option e.op

instance : HasEffect e (e :: effs) where
    inject := fun c => @OU.Leaf e effs c
    project := fun ou => match ou with
                         | .Leaf c => Option.some c
                         | .Node ou' => Option.none

instance [HasEffect e effs] : HasEffect e (z :: effs) where
    inject := fun x => OU.Node (@HasEffect.inject e effs _ x)
    project := fun ou => match ou with
                         | .Leaf c => Option.none
                         | .Node ou' => HasEffect.project ou'


end Effect



inductive Freer.{u} (effs : List Effect.{u}) : Type u → Type (u+1) where
    | Pure : a → Freer effs a
    | Impure : {x : Type u} → Effect.OU effs x → (x → Freer effs a) → Freer effs a

namespace Freer

open Effect

-- lift into Freer
def send {e : Effect} {effs : List Effect} [HasEffect e effs] (sendop : e.op) : Freer effs (e.ret sendop) :=
    @Freer.Impure effs (e.ret sendop) _ (HasEffect.inject sendop) .Pure

-- Sometimes you have a monad with some effects but you need to pass it into a function
-- with additional effects (see the Catch/Throw higher-order effect for instance).
def weaken.{u} {g : Effect.{u}} {effs : List Effect.{u}} : Freer effs a → Freer (g :: effs) a
    | .Pure a => .Pure a
    | .Impure ou next => .Impure (OU.Node ou) (fun x => weaken (next x))

def FreerAlg.{u,v} (effs : List Effect.{u}) (a : Type v) := {x : Type u} → (OU effs x) → (x → a) → a

def freerCata {a : Type (u+1)} (alg : FreerAlg effs a) (w : Freer effs a) : a :=
    match w with
    | .Pure a => a
    | .Impure gx next => alg gx (fun x => freerCata alg (next x))

def freerMap {a b : Type u} (f : a → b) (w : Freer effs a) : Freer effs b :=
    match w with
    | .Pure a => .Pure (f a)
    | .Impure gx next => .Impure gx (fun x => freerMap f (next x))

instance : Functor (Freer effs) :=
    { map := freerMap }

-- foldOver is basically freerCata + freerMap
def foldOver {a : Type u} {b : Type v} {effs : List Effect.{u}} (pf : a → b) (alg : FreerAlg.{u,v} effs b) : Freer effs a → b
    | .Pure a => pf a
    | @Freer.Impure _ a _ gx next => alg gx (fun x => @foldOver a b effs pf alg (next x))
    

/-
-- alternate implementation of bind using a fold, similar to the "Hefty Algebras" paper
--
-/
def bindFreer {a b : Type u} (m : Freer effs a) (f : a → Freer effs b) : Freer effs b :=
    --@foldOver a (Freer effs b) effs f .Impure m
    match m with
    | .Pure a => f a
    | .Impure gx next => Freer.Impure gx (fun z => bindFreer (next z) f)

def pureFreer {α : Type u} (a : α) : Freer effs α := Freer.Pure a



-- Handler is the handler for a specific effect: ret is for Pure constructors
-- and handle is for impure constructors. The result has an 'inp' type so that the  monad can
-- take inputs (a state monad for example). You can make inp Unit for no input.
--  - a is the type returned from a Pure
--  - b is the monad result type. It may be that a=b but not always.
structure Handler (a : Type u) (b : Type u) (e : Effect) (effs : List Effect) (inp : Type u) where
   (ret : a → inp → Freer effs b)
   (handle : FreerAlg (e :: effs) (inp → Freer effs b))


-- Interpret a Freer monad. You must provide an "interpreter" which takes commands of type c
-- and produces monads of the final type n.  This runs the interpreter on a command
-- in the Impure constructor and combines it with the next chunk of the Freer monad
-- by using a definition of bind for the final monad n.
def handleFreer {a b : Type u} {e : Effect} {effs : List Effect} {inp : Type u} 
    (handler : Handler a b e effs inp) (m : Freer (e :: effs) a) : inp → Freer effs b :=
    foldOver handler.ret handler.handle m


-- After handling all effects, you'll have a Freer [] a left over, use
-- runEff at the end to extract the result.
-- example : runEff <| h2 <| h1 m

def runEff : Freer [] a → a
    | .Pure x => x
    -- shouldn't ever have an Impure constructed
    --| .Impure ou next => match ou with | .Leaf c => Fin.elim0 (ULift.down c)


end Freer

instance : Monad (Freer effs) where
    pure := Freer.pureFreer
    bind := Freer.bindFreer

instance : Pure (Freer effs) where
    pure := Freer.pureFreer

instance : Bind (Freer effs) where
    bind := Freer.bindFreer
