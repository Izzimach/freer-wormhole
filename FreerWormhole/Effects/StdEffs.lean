
import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.Heff

open Freer Effect

section Effect





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




end Effect


section HEffect


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

    



end HEffect




open HEffect


def transact
    [HasHEffect (hLifted (StateEff Nat)) heffs]
    [HasHEffect (hLifted ThrowEff) heffs]
    [HasHEffect (CatchHEff (onlyRet Unit)) heffs]
      : Hefty heffs Nat :=
    do
    putH 1
    catchHUnit (do putH 2; throwH) (pure ())
    getH

def elabTransact : Elaboration [ CatchHEff (onlyRet Unit), hLifted ThrowEff, hLifted (StateEff Nat), hLifted NilEffect]
                               [ ThrowEff, StateEff Nat] :=
    eCatch1 <| (eLift ThrowEff) <| (eLift (StateEff Nat)) <| @eNil [ThrowEff, StateEff Nat]

def runTransact : Freer [ThrowEff, StateEff Nat] a → (Option a × Nat) :=
    let h1 := fun m => handleFreer throwHandler m ()
    let h2 := fun m => handleFreer stateHandler m (3 : Nat)
    fun m => runEff <| h2 <| h1 m

#eval runTransact (elaborate elabTransact transact)
