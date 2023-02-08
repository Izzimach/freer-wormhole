
import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.Heff


namespace StdEffs

open Freer Effect HEffect

--
-- Standard State Effect, with get and put
--

inductive StateOp (a : Type) : Type 1 where
    | Put : a → StateOp a 
    | Get : StateOp a

def StateEff (a : Type) : Effect :=
    {
        op := StateOp a,
        ret := fun op => match op with
                         | .Put _ => Unit
                         | .Get   => a
    }

def stateHandler {s : Type} : Handler a (a × s) (StateEff s) effs s :=
    {
        ret := fun a s => Freer.Pure ⟨a,s⟩,
        handle := fun ou next s =>
            match ou with
            | .Leaf l => match l with
                         | .Put x => next () x
                         | .Get   => next s s
            | .Node ou' => .Impure ou' (fun x => next x s)
    }

def runState {s x : Type} (init : s) : Freer (StateEff s :: effs) x → Freer effs (x × s) :=
    fun m => handleFreer (@stateHandler x effs s ) m init

def get {s : Type} {effs : List Effect} [HasEffect (StateEff s) effs] : Freer effs ((StateEff s).ret StateOp.Get) :=
    @send (StateEff s) effs _ StateOp.Get

def getH { s : Type} {heffs : List HEffect} [HasHEffect (hLifted (StateEff s)) heffs] : Hefty heffs s :=
    @hLift (StateEff s) _ _ StateOp.Get

def put {s : Type} {effs : List Effect} [HasEffect (StateEff s) effs] (x : s) : Freer effs ((StateEff s).ret (StateOp.Put x)) :=
    @send (StateEff s) effs _ (StateOp.Put x)

def putH {s : Type} {heffs : List HEffect} [HasHEffect (hLifted (StateEff s)) heffs] (x : s) : Hefty heffs Unit :=
    @hLift (StateEff s) _ _ (StateOp.Put x)




--
-- Identity effect, used for no-op or placeholder. This is different from the
-- NilEffect which is used to terminate effects chains and is more like a "not effect"
--

inductive Noop : Type u where
    | Noop

def NoopEffect : Effect :=
    {
        op := Noop,
        ret := fun _ => PUnit
    }

def noopEffHandler {a : Type} : Handler a a NoopEffect effs PUnit :=
    {
        ret := fun a _ => Freer.Pure a,
        handle := fun ou next _ =>
            match ou with
            | .Leaf l => next PUnit.unit PUnit.unit
            | .Node ou' => .Impure ou' (fun x => next x PUnit.unit)
    }

def runNoopEff {effs : List Effect} : Freer (NoopEffect :: effs) x → Freer effs x :=
    fun m => handleFreer (@noopEffHandler effs x) m PUnit.unit


def noop {effs : List Effect} [HasEffect NoopEffect effs] : Freer effs PUnit :=
    @send NoopEffect effs _ Noop.Noop

def noopH {heffs : List HEffect} [HasHEffect (hLifted NoopEffect) heffs] : Hefty heffs PUnit :=
    @hLift NoopEffect heffs _ Noop.Noop

--
-- A generic IO effect to run an (mostly?) arbitrary IO effect
--


inductive IOX : Type 1 where
    | IOOp : (a : Type) → IO a → IOX

def IOEffect : Effect :=
    {
        op := IOX,
        ret := fun z => match z with
                        | IOX.IOOp a m => a
    }

def runIOEff {a : Type} : Freer [IOEffect] a → IO a
    | .Pure a => pure a
    | .Impure (.Leaf l) next =>
        match l with
        | .IOOp _ m =>    m >>= (fun x => runIOEff (next x))

-- special case of runIOEff for Unit, because of odd lifting
def runIOEffUnit : Freer [IOEffect] PUnit → IO Unit
    | .Pure _ => pure ()
    | .Impure (.Leaf l) next =>
        match l with
        | .IOOp _ m =>    m >>= (fun x => runIOEffUnit (next x))

def ioEff0 {a : Type} {effs : List Effect} [HasEffect IOEffect effs] (m : IO a) : Freer effs PUnit :=
    Freer.Impure (@HasEffect.inject IOEffect effs _ <| IOX.IOOp a m) (fun x => Freer.Pure PUnit.unit)

def ioEff {a : Type} {effs : List Effect} [HasEffect IOEffect effs] (m : IO a) : Freer effs a :=
    Freer.Impure (@HasEffect.inject IOEffect effs _ <| IOX.IOOp a m) (fun x => Freer.Pure x)


def ioEffH0 {heffs : List HEffect} [HasHEffect (hLifted IOEffect) heffs] (m : IO Unit) : Hefty heffs Unit :=
    hBind (@hLift IOEffect heffs _ (IOX.IOOp Unit m)) (fun _ => hPure PUnit.unit)

def ioEffH {a : Type} {heffs : List HEffect} [HasHEffect (hLifted IOEffect) heffs] (m : IO a) : Hefty heffs a :=
    @hLift IOEffect heffs _ (IOX.IOOp a m)

end StdEffs


namespace StdHEffs

open Freer Effect HEffect

inductive ThrowOp : Type u where
    | Throw : String → ThrowOp

def ThrowEff : Effect :=
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

def runThrow : Freer (ThrowEff :: effs) x → Freer effs (Option x) := fun m => handleFreer throwHandler m ()

def throwH {heffs : List HEffect} [HasHEffect (hLifted ThrowEff) heffs] : Hefty heffs PUnit :=
    hBind (@hLift ThrowEff _ _ (ThrowOp.Throw "argh"))
          (fun _ => hPure ())




-- "Universe-of-Types" basically mapping from values in one type to types in that same universe
structure UoT : Type 1 where
    (choice : Type)
    (uotResult : choice → Type)

-- Used with catch; (CatchHEff (onlyRet a)) is a try/catch that always return a, on success OR failure
def onlyRet (a : Type) : UoT :=
    {
        choice := PUnit,
        uotResult := fun _ => a
    }



inductive CatchOp (catchDispatch : UoT) : Type u where
    | Catch : catchDispatch.choice → CatchOp catchDispatch

inductive ExceptResult : Type u where
    | Success : ExceptResult
    | Failure : ExceptResult

def CatchFork (a : Type) : Effect :=
    {
        -- possible values to pass to the fork, to choose which fork
        op := ExceptResult,
        -- return type from various forks, these can be different or the same
        ret := fun z => match z with
                        | .Success => a   -- success returns catch result
                        | .Failure => a
    }

def CatchHEff (dispatch : UoT) : HEffect :=
    {
        cmd := CatchOp dispatch,
        fork := fun op => CatchFork (dispatch.uotResult op.1),
        retH := fun e => dispatch.uotResult e.1
    }

def catchH {result : Type} {heffs : List HEffect} [HasHEffect (CatchHEff (onlyRet result)) heffs] 
      (run : Hefty heffs result)
      (onError : Hefty heffs result) : Hefty heffs result :=
    @hSend heffs (CatchHEff (onlyRet result)) _ (CatchOp.Catch PUnit.unit)
        (fun pz => match pz with
                   | ExceptResult.Success => run
                   | .Failure => onError)


def eCatch : Elaboration [CatchHEff (onlyRet Nat)] (ThrowEff :: effs) :=
    fun op phi next => match op with
                       | .Leaf c => match c with
                                    | .Catch v => let m₁ := phi .Success
                                                  let m₂ := phi .Failure
                                                  let r₁ := runThrow m₁
                                                  let r₂ := fun (z : Option _) => match z with
                                                                     | Option.none => bindFreer m₂ next
                                                                     | Option.some x => next x
                                                  (weaken r₁) >>= r₂


def elabCatch : Elab1 (CatchHEff (onlyRet Unit)) heffs (ThrowEff :: effs) :=
    fun elab0 =>
    fun op phi next =>
        match op with
        | .Leaf c =>
            match c with
            | .Catch PUnit.unit =>
                let r₁ := runThrow (phi .Success)
                let r₂ := fun (z : Option _) => match z with
                                    | Option.none => bindFreer (phi .Failure) next
                                    | Option.some x => next x
                (weaken r₁) >>= r₂
        | .Node hou' => elab0 hou' phi next



end StdHEffs



section testEffs

open Freer Effect HEffect StdEffs StdHEffs


def transact
    [HasHEffect (hLifted (StateEff Nat)) heffs]
    [HasHEffect (hLifted ThrowEff) heffs]
    [HasHEffect (CatchHEff (onlyRet Unit)) heffs]
      : Hefty heffs Nat :=
    do
    putH 1
    catchH
        (do putH 2; throwH)
        (do putH 3; pure ())
    getH

def elabTransact : Elaboration [ CatchHEff (onlyRet Unit), hLifted ThrowEff, hLifted (StateEff Nat)]
                               [ ThrowEff, StateEff Nat] :=
    elabCatch
    <| elabEff ThrowEff
    <| elabLast (StateEff Nat)

def runTransact : Freer [ThrowEff, StateEff Nat] a → (Option a × Nat) :=
    fun m => runEff <| runState 3 <| runThrow m

#eval runTransact <| elaborate elabTransact <| transact

def printArghs [HasHEffect (hLifted IOEffect) heffs] [HasHEffect (hLifted NoopEffect) heffs] : Hefty heffs PUnit := do
    ioEffH0 (IO.println "argh")
    ioEffH0 (IO.println "argh")
    noopH
    ioEffH0 (IO.println "argh")

-- Higher order effects need an elaboration phase followed by a run phase.
-- Here we defined the elaboration phase.
def elabDump : Elaboration [hLifted NoopEffect, hLifted IOEffect] [NoopEffect, IOEffect] :=
     elabEff NoopEffect
     <| elabLast IOEffect


#eval runIOEffUnit <| runNoopEff <| elaborate elabDump <| printArghs

end testEffs