--
-- A basic freer monad. Based on various haskell libraries including freer-simple and
-- the paper "Freer Monads, More Extensible Effects" by Oleg Kiselyov and Hiromi Ishii
--

-- The Freer monad doesn't contain actual executable code, but instead
-- stores either a result value (Pure) or an effect plus continuation (Impure).
--

import FreerWormhole.WType

open pfunctor W_type

structure Effect : Type (u+1) where
   (op : Type u)
   (ret : op → Type u)

inductive OU : List Effect.{u} → Type u → Type (u+1) where
| Leaf {eff : Effect.{u}} {effs : List Effect.{u}} : (c : eff.op) → OU (eff :: effs) (eff.ret c)
| Node {eff : Effect} {effs : List Effect} : OU effs x → OU (eff :: effs) x

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

def decompOU {e : Effect} {effs : List Effect} (ou : OU (e :: effs) x) : Sum (OU effs x) (e.op) :=
    match ou with
    | .Leaf x => Sum.inr x
    | .Node ou' => Sum.inl ou'                

inductive Freer (effs : List Effect.{u}) : Type u → Type (u+1) where
    | Pure : a → Freer effs a
    | Impure : {x : Type u} → OU effs x → (x → Freer effs a) → Freer effs a

-- lift into Freer
def send.{u} {g : Effect.{u}} {effs : List Effect.{u}} [HasEffect g effs] (ga : g.op) : Freer effs (g.ret ga) :=
    @Freer.Impure effs (g.ret ga) _ (HasEffect.inject ga) .Pure

def weaken.{u} {g : Effect.{u}} {effs : List Effect.{u}} : Freer effs a → Freer (g :: effs) a
| .Pure a => .Pure a
| .Impure ou next => .Impure (OU.Node ou) (fun x => weaken (next x))

def FreerAlg.{u} (effs : List Effect.{u}) (a : Type v) := {x : Type u} → (OU effs x) → (x → a) → a

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
def foldOver {a : Type u} {b : Type v} {effs : List Effect.{u}} (pf : a → b) (alg : FreerAlg effs b) : Freer effs a → b
    | .Pure a => pf a
    | @Freer.Impure _ a _ gx next => alg gx (fun x => @foldOver a b effs pf alg (next x))
    


/-
-- alternate implementation of bind using a fold, similar to the "Hefty Algebras" paper
--
-/
def bindFreer {effs : List Effect.{u}} (m : Freer effs a) (f : a → Freer effs b) : Freer effs b :=
    @foldOver a (Freer effs b) effs f .Impure m

def pureFreer {α : Type} (a : α) : Freer effs α := Freer.Pure a


instance : Monad (Freer effs) where
    pure := pureFreer
    bind := bindFreer


-- Handler is the handler for a specific effect: ret is for Pure constructors
-- and handle is for impure constructors. The result has an 'inp' type so that the  monad can
-- take inputs (a state monad for example). You can make inp Unit for no input.
--  - a is the type returned from a Pure
--  - b is the monad result type. It may be that a=b but not always.
structure Handler (a b : Type u) (e : Effect.{u}) (effs : List Effect.{u}) (inp : Type u) where
   (ret : a → inp → Freer effs b)
   (handle : FreerAlg (e :: effs) (inp → Freer effs b))

-- Interpret a Freer monad. You must provide an "interpreter" which takes commands of type c
-- and produces monads of the final type n.  This runs the interpreter on a command
-- in the Impure constructor and combines it with the next chunk of the Freer monad
-- by using a definition of bind for the final monad n.
def handleFreer {a b : Type u} {e : Effect} {effs : List Effect} {inp : Type u} 
    (handler : Handler a b e effs inp) (m : Freer (e :: effs) a) : inp → Freer effs b :=
    foldOver handler.ret handler.handle m



def NilEffect.{u} : Effect.{u} :=
    {
        -- we use Fin 0 as a stand-in for bottom
        op := ULift <| Fin 0,
        ret := fun _ => ULift <| Fin 0
    }

def NilHandler : Handler.{u} a a NilEffect effs PUnit :=
    {
        ret := fun a _ => .Pure a,
        handle := fun ou next s =>
            match ou with
            | .Leaf l => Fin.elim0 (ULift.down l)
            | .Node ou' => .Impure ou' (fun x => next x s)
    }

def runEff : Freer [] a → a
    | .Pure x => x
    -- shouldn't ever have an Impure constructed
    --| .Impure ou next => match ou with | .Leaf c => Fin.elim0 (ULift.down c)

--
-- higher-order effects
--

structure HEffect.{u} : Type (u+1) where
    (cmd : Type u)
    (fork : cmd  → Effect.{u})
    (retH : cmd → Type u)


-- Choose one HEffect from a list of them.
inductive HOU.{u} : List HEffect → (ret : Type u) → Effect.{u} → Type (u+1) where
    | Leaf : (c : heff.cmd) → HOU (heff :: heffs) (heff.retH c) (heff.fork c)
    | Node : HOU heffs c fork → HOU (_ :: heffs) c fork


inductive Hefty.{u} : List HEffect.{u} → Type u → Type (u+2) where
| Pure {a : Type u} : a → Hefty h a
| Impure {x : Type u} {e : Effect.{u}} : HOU h x e → ((c : e.op) → Hefty h (e.ret c)) → (x → Hefty h a) → Hefty h a

class HasHEffect (h : HEffect) (heffs : List HEffect) where
    inject : (c : h.cmd) → HOU heffs (h.retH c) (h.fork c)

instance : HasHEffect h (h :: heffs) where
    inject := fun c => @HOU.Leaf h heffs c

instance [HasHEffect h heffs] : HasHEffect h (z :: heffs) where
    inject := fun c => HOU.Node (@HasHEffect.inject h heffs _ c)

def decompHOU {eff : Effect} {heff : HEffect} {heffs : List HEffect} (hou : HOU (heff :: heffs) x eff) : Sum (HOU heffs x eff) heff.cmd :=
    match hou with
    | .Leaf c => Sum.inr c
    | .Node hou' => Sum.inl hou'


def hPure (val : a) : Hefty h a := .Pure val

def hBind (m : Hefty h a) (f : a → Hefty h b) : Hefty h b :=
    match m with
    | .Pure a => f a
    | .Impure ou psi next => .Impure ou psi (fun x => hBind (next x) f)

instance : Monad (Hefty effs) where
    pure := hPure
    bind := hBind

def hLifted (eff : Effect.{u}) : HEffect := 
    {
        cmd := eff.op,
        fork := fun _ => NilEffect.{u},
        retH := eff.ret
    }

def hLift {eff : Effect} [HasHEffect (hLifted eff) heffs] (c : eff.op) : Hefty heffs (eff.ret c) :=
    -- yikes
    @Hefty.Impure heffs _ (eff.ret c) NilEffect (@HasHEffect.inject (hLifted eff) heffs _ c) (fun f0 => Fin.elim0 (ULift.down f0)) hPure


def HeftyAlg (heffs : List HEffect) (a : Type u) := {x : Type u} → {e : Effect} → (c : HOU heffs x e) → (x → a) → a


inductive ThrowOp : Type u where
| Throw : String → ThrowOp

def ThrowEff : Effect.{u} :=
    {
        op := ThrowOp,
        ret := fun _ => ULift <| Fin 0
    }

def throwHandler : Handler a (Option a) ThrowEff effs Unit := 
    {
        ret := fun a () => Freer.Pure (Option.some a),
        handle := fun ou next () => match ou with
                                    | .Leaf z => match z with | .Throw err => Freer.Pure Option.none
                                    | .Node ou' => Freer.Impure ou' (fun x => next x ())
    }

def throwH {heffs : List HEffect} [HasHEffect (hLifted ThrowEff) heffs] : Hefty heffs PUnit :=
    hBind (@hLift _ ThrowEff _ (ThrowOp.Throw "argh"))
          (fun _ => hPure ())

-- "Universe-of-Types" basically mapping from values in one type to types in that same universe
structure UoT : Type (u+1) where
    (val : Type u)
    (toT : val → Type u)

def onlyRet (a : Type u) : UoT.{u} :=
    {
        val := PUnit,
        toT := fun _ => a
    }

inductive CatchOp.{u} (uni : UoT.{u}) : Type (u) where
| Catch : uni.val → CatchOp uni

inductive ExceptResult : Type u where
| Success : ExceptResult
| Failure : ExceptResult

def CatchFork (a : Type u) : Effect.{u} :=
    {
        -- possible values to pass to the fork, to choose which fork
        op := ExceptResult,
        -- return type from various forks, these can be different or the same
        ret := fun z => match z with
                        | .Success => a   -- success returns catch result
                        | .Failure => a
    }

def CatchHEff.{u} (uni : UoT.{u}) : HEffect.{u} :=
    {
        cmd := CatchOp uni,
        fork := fun e => CatchFork (uni.toT e.1),
        retH := fun e => (uni.toT e.1)
    }

def catchHUnit {heffs : List HEffect} [HasHEffect (CatchHEff (onlyRet Unit)) heffs] 
      (run : Hefty heffs Unit)
      (onError : Hefty heffs Unit) : Hefty heffs Unit :=
    Hefty.Impure
        (@HasHEffect.inject (CatchHEff (onlyRet Unit)) heffs _ (CatchOp.Catch ()))
        (fun pz => match pz with
                   | .Success => run
                   | .Failure => onError)
        (fun z => hPure ())

-- an algebra for Hefty h a
def algH.{u} (heffs : List HEffect.{u}) (f : Type u → Type (u+1)) : Type (u+1) :=
    {x a : Type u} → {e : Effect.{u}} → (c : HOU heffs x e) → ((s : e.op) → f ((e.ret s))) → (x → f a) → f a

def cataH.{u} {heffs : List HEffect.{u}} {a : Type u} {f : Type u → Type (u+1)} (pf : {x : Type u} → x → f x) (alg : algH heffs f) (t : Hefty heffs a) : f a :=
    match t with
    | Hefty.Pure x => pf x
    | Hefty.Impure ou psi next => alg ou (fun x => cataH pf alg (psi x)) (fun x => cataH pf alg (next x))


def Elaboration (heffs : List HEffect) (effs : List Effect) : Type (u+1) := algH heffs (Freer effs)

def elaborate (e : Elaboration heffs eff) (h : Hefty heffs a) : Freer eff a := cataH Freer.Pure e h

-- Elaboration eloborations a whole list of HEffects into a Freer of effects.
-- Elab1 adds elaboration for a single HEffect onto an Elaboration. You can use this to build
-- up an Elaboration by chaining of several Elab1 terms.
def Elab1 (heff : HEffect) (heffs : List HEffect) (effs : List Effect) : Type (u+1) := Elaboration heffs effs → Elaboration (heff :: heffs) effs

/-def hCatch (e : Type u) (m : (x : Type u) → Hefty [CatchHEff e] x) (err : (x : Type u) → Hefty [CatchHEff e] x) : Hefty [CatchHEff e] a :=
    @Hefty.Impure [CatchHEff Nat] a _ (@CatchOp.Catch a)
             (fun x fork => match fork with
                            | .Success a => m x
                            | .Failure err => err x)
             (fun z => hPure z)-/

inductive StateOp (a : Type u) : Type u where
| Put : a → StateOp a 
| Get : StateOp a

def StateEff (a : Type u) : Effect :=
    {
        op := StateOp a,
        ret := fun op => match op with
                         | .Put _ => PUnit
                         | .Get   => a
    }

def stateHandler {s : Type u} : Handler.{u} a (a × s) (StateEff s) effs s :=
    {
        ret := fun a s => Freer.Pure ⟨a,s⟩,
        handle := fun ou next s =>
            match ou with
            | .Leaf l => match l with
                         | .Put x => next PUnit.unit x
                         | .Get   => next s s
            | .Node ou' => .Impure ou' (fun x => next x s)
    }

def get {s : Type u} {effs : List Effect} [HasEffect (StateEff s) effs] : Freer effs ((StateEff s).ret StateOp.Get) :=
    @send (StateEff s) effs _ StateOp.Get

def getH { s : Type u} {heffs : List HEffect} [HasHEffect (hLifted (StateEff s)) heffs] : Hefty heffs s :=
    @hLift _ (StateEff s) _ StateOp.Get

def put {s : Type u} {effs : List Effect} [HasEffect (StateEff s) effs] (x : s) : Freer effs ((StateEff s).ret (StateOp.Put x)) :=
    @send (StateEff s) effs _ (StateOp.Put x)

def putH {s : Type u} {heffs : List HEffect} [HasHEffect (hLifted (StateEff s)) heffs] (x : s) : Hefty heffs PUnit :=
    @hLift _ (StateEff s) _ (StateOp.Put x)

def eCatch : Elaboration [CatchHEff (onlyRet Nat)] (ThrowEff :: effs) :=
    fun op phi next => match op with
                       | .Leaf c => match c with
                                    | .Catch v => let m₁ := phi .Success
                                                  let m₂ := phi .Failure
                                                  let r₁ := handleFreer throwHandler m₁
                                                  let r₂ := fun (z : Option _) => match z with
                                                                     | Option.none => bindFreer m₂ next
                                                                     | Option.some x => next x
                                                  (weaken (r₁ ())) >>= r₂


def eCatch1 : Elab1 (CatchHEff (onlyRet Unit)) heffs (ThrowEff :: effs) :=
    fun elab0 =>
        fun op phi next => match op with
                           | .Leaf c => match c with
                                        | .Catch v =>
                                                  let m₁ := phi .Success
                                                  let m₂ := phi .Failure
                                                  let r₁ := handleFreer throwHandler m₁
                                                  let r₂ := fun (z : Option _) => match z with
                                                                     | Option.none => bindFreer m₂ next
                                                                     | Option.some x => next x
                                                  (weaken (r₁ ())) >>= r₂
                           | .Node hou' => elab0 hou' phi next

def eLift (eff : Effect) [HasEffect eff effs] : Elab1 (hLifted eff) heffs effs :=
    fun elab0 => 
        fun op phi next => match op with
                           | .Leaf c => Freer.Impure (HasEffect.inject c) next
                           | .Node hou' => elab0 hou' phi next

-- a higher-order effect that should not be able to be constructed, used to terminate
-- Heff elaboration
def eNil : Elaboration [hLifted NilEffect] effs :=
    fun c phi next => match c with
                      | .Leaf x => Fin.elim0 (ULift.down x)
    

def transact
    [HasHEffect (hLifted (StateEff Nat)) heffs]
    [HasHEffect (hLifted ThrowEff) heffs]
    [HasHEffect (CatchHEff (onlyRet Unit)) heffs]
      : Hefty heffs Nat := do
    putH 1
    catchHUnit (do throwH; putH 2) (pure ())
    getH

def elabTransact : Elaboration [ CatchHEff (onlyRet Unit), hLifted ThrowEff, hLifted (StateEff Nat), hLifted NilEffect]
                               [ ThrowEff, StateEff Nat] :=
    eCatch1 <| (eLift ThrowEff) <| (eLift (StateEff Nat)) <| @eNil [ThrowEff, StateEff Nat]

def runTransact : Freer [ThrowEff, StateEff Nat] a → (Option a × Nat) :=
    let h1 := fun m => handleFreer throwHandler m ()
    let h2 := fun m => handleFreer stateHandler m (3 : Nat)
    fun m => runEff <| h2 <| h1 m

#eval runTransact (elaborate elabTransact transact)
