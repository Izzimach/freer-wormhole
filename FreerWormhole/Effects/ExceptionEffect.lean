import Lean

import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole
import FreerWormhole.Skeleton
import FreerWormhole.Automata
import FreerWormhole.MetaProgramGraph


open Effect EffM SupportsEffect
open HEffect HEffM SupportsHEffect

open Wormhole WormholeAutomata MetaProgramGraph

open Lean Elab Term

namespace ExceptionEffect


inductive ThrowOp : Type → Type 1 where
    | Throw : e → ThrowOp e

def ThrowEffect (e : Type) : Effect :=
    {
        op := ThrowOp e,
        ret := fun _ => ULift <| Fin 0
    }

-- handler runs the code. Returns Sum.inr if no error, or Sum.inl if there is an error.
def throwHandler : Handler a (Sum e a) (ThrowEffect e) effs Unit := 
    {
        ret := fun a () => .Pure (.inr a),
        handle := fun ou next () =>
            match decompOU ou with
            | .inl ou' => .Impure ou' (fun x => next x ())
            | .inr ⟨z,h⟩ => match z with | .Throw err => .Pure (.inl err)
    }

def runThrow {err : Type} : EffM (ThrowEffect err :: effs) x → EffM effs (Sum err x) := fun m => handleEffect throwHandler m ()

-- This is throwEff since throw is already used for MonadFail.
def throwEff {ErrorType : Type} [Monad m] [SupportsEffect (ThrowEffect ErrorType) m] (msg : ErrorType): m PUnit :=
    @send (ThrowEffect ErrorType) m _ (ThrowOp.Throw msg) >>= (fun _ => pure ())
          


-- "Universe-of-Types" basically mapping from values in one type to types in that same universe
structure UoT : Type 1 where
    (choice : Type)
    (uotResult : choice → Type)

-- Used with catch; (ExceptionHEffect (onlyRet a)) is a try/catch that always return a, on success OR failure
def onlyRet (a : Type) : UoT :=
    {
        choice := PUnit,
        uotResult := fun _ => a
    }



inductive CatchOp (catchDispatch : UoT) : Type 1 where
    | Catch : catchDispatch.choice → CatchOp catchDispatch

inductive ExceptResult : Type 1 where
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

def ExceptionHEffect (dispatch : UoT) : HEffect :=
    {
        cmd := CatchOp dispatch,
        fork := fun op => CatchFork (dispatch.uotResult op.1),
        retH := fun e => dispatch.uotResult e.1
    }

def catchH {result : Type} [Monad m] [SupportsHEffect (ExceptionHEffect (onlyRet result)) m] 
      (run : m result)
      (onError : m result) : m result :=
    @hSend (ExceptionHEffect (onlyRet result)) m _ (CatchOp.Catch PUnit.unit)
        (fun pz => match pz with
                   | .Success => run
                   | .Failure => onError)



def elabCatch : Elab1 (ExceptionHEffect (onlyRet Unit)) heffs (ThrowEffect err :: effs) :=
    fun elab0 =>
        fun op phi next =>
            match decompHOU op with
            | Sum.inr ⟨c,h⟩ =>
                match c with
                | .Catch PUnit.unit =>
                    let phi' := show ((s : (CatchFork PUnit).op) → (EffM (ThrowEffect err :: effs) (ret (CatchFork PUnit) s))) by
                        rename_i result eff2
                        have h4 : eff2 = CatchFork PUnit := by rw [←h.right]; unfold fork; unfold ExceptionHEffect; unfold onlyRet; simp
                        rw [←h4]
                        exact phi
                    let r₁ : EffM effs (Sum err Unit) := runThrow (phi' ExceptResult.Success)
                    let r₂ := fun (z : Sum err Unit) => match z with
                                        | .inl err =>
                                            let h4 : retH (ExceptionHEffect (onlyRet Unit)) (CatchOp.Catch PUnit.unit) = ret (CatchFork PUnit) ExceptResult.Failure :=
                                                by unfold retH; unfold ret; unfold ExceptionHEffect; unfold onlyRet; unfold CatchFork; simp
                                            EffM.bindEff (phi' ExceptResult.Failure) (show _ by rw [←h4, h.left]; exact next)
                                        | .inr x => next (show _ by rw [←h.left]; exact x)
                    (weaken r₁) >>= r₂
            | Sum.inl hou' => elab0 hou' phi next

def ExceptionEffectSkeletonProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"ThrowEffect", effSyntaxMode `(fun (op : Type 1) (x : op) => "Throw")⟩]
        [
        ⟨"ExceptionHEffect", fun heff cmd fork rec => do
            let forks ← unfoldFork fork
            match forks with
            | .some v => do
                let evals ← v.mapM (rec true #[])
                v.forM (fun z => logInfo <| toMessageData z)
                --let evals : Array (TSyntax `term) := evals.map (TSyntax.mk)
                --`("catchEff " ++ toString $(List.length v[ $evals,* ]))
                let vLen := toString (v.size)
                `("catchEff " ++ $(Syntax.mkStrLit vLen))
            | .none => `("catchEff?")⟩
        ]
        []


def ExceptionEffectAutomataProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"ThrowEffect", effSyntaxMode `(fun (op : Type 1) x => labeledNode "Throw")⟩]
        [⟨"ExceptionHEffect", fun heff cmd fork rec => do
            let forks ← unfoldFork fork
            match forks with
            | .some v => do
                let evals ← v.mapM (rec true #[])
                v.forM (fun z => logInfo <| toMessageData z)
                --let evals : Array (TSyntax `term) := evals.map (TSyntax.mk)
                --`("catchEff " ++ toString $(List.length v[ $evals,* ]))
                let vLen := toString (v.size)
                `("catchEff " ++ $(Syntax.mkStrLit vLen))
            | .none => `("catchEff?")⟩
        ]
        []

def ExceptionEffectProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"ThrowEffect", effSyntaxMode `(fun (op : Type 1) (x : ThrowOp) => basicStep ("[[throw]]"))⟩]
        [⟨"ExceptionHEffect", fun heff cmd fork rec => do
            let forks ← unfoldFork fork
            match forks with
            | .some v => do
                let evals ← v.mapM (rec true #[])
                v.forM (fun z => logInfo <| toMessageData z)
                --let evals : Array (TSyntax `term) := evals.map (TSyntax.mk)
                --`("catchEff " ++ toString $(List.length v[ $evals,* ]))
                let vLen := toString (v.size)
                `("catchEff " ++ $(Syntax.mkStrLit vLen))
            | .none => `("catchEff?")⟩
        ]
        []



end ExceptionEffect
