-- HEffect used for generating processes, specifically forking off threads
import Lean

import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Effects.IOEffect

import FreerWormhole.Wormhole
import FreerWormhole.MetaProgramGraph
import SolifugidZ.ProgramGraph

namespace MultithreadHEffect

open EffM HEffM Effect HEffect
open IOEffect

open Lean Elab Expr Meta Term
open Wormhole MetaProgramGraph ProgramGraph

inductive MultithreadCmd : Type 1 where
    | ForkThreads : Nat → MultithreadCmd

def ForkThreadEffect (n : Nat) : Effect :=
    {
        op := ULift (Fin n)
        ret := fun _ => PUnit
    }

-- An HEffect used mainly for forking off concurrent threads.
def MultithreadHEffect : HEffect :=
    {
        cmd := MultithreadCmd
        fork := fun g => match g with
                         | .ForkThreads n => ForkThreadEffect n
        retH := fun g => match g with
                         | .ForkThreads _ => PUnit
    }

def forkThreads [Monad m] [SupportsHEffect MultithreadHEffect m]
    (processes : List (m PUnit)) : m PUnit :=
    @SupportsHEffect.hSend MultithreadHEffect m _ (.ForkThreads processes.length) (fun ix => processes.get (ULift.down ix))

       
def runThreads {n : Nat} {effs : List Effect} [HasEffect IOEffect effs]
    (pr : (ULift (Fin n)) → EffM effs PUnit) (runner : EffM effs PUnit → IO Unit) (ix : Fin n) : EffM effs PUnit := do
        let _ ← liftIO <| IO.asTask (runner <| pr (ULift.up ix)) Task.Priority.dedicated
        if h : ix.val ≠ 0
        then runThreads pr runner (Fin.mk (Nat.pred ix.val) (by apply (@Nat.lt_of_lt_of_le _ ix.val n); apply Nat.pred_lt h; apply Nat.le_of_lt; exact ix.isLt))
        else pure ()
    termination_by runThreads _ _ ix => ix.val

def elabMultithread {effs : List Effect} {heffs : List HEffect} [HasEffect IOEffect effs]
    (runner : EffM effs PUnit → IO Unit)
    : Elab1 MultithreadHEffect heffs effs :=
    fun elab0 =>
    fun op phi next =>
        match decompHOU op with
        | Sum.inr ⟨c,h⟩ => do
                let phi' : (s : (MultithreadHEffect.fork c).op) → EffM effs ((MultithreadHEffect.fork c).ret s) := by rename_i e; rw [h.right]; exact phi
                if hz : c.1 ≠ 0
                then runThreads phi' runner (@Fin.mk c.1 (Nat.pred c.1) (Nat.pred_lt hz))
                else pure ()
                next (show _ by rw [←h.left]; exact ())
        | Sum.inl hou' => elab0 hou' phi next

def interleaveForks (prog : Syntax) (forks : List Syntax) : TermElabM Syntax :=
    match forks with
    | .cons h t => do
        let h' ← `(concurrentPrograms $(TSyntax.mk prog) $(TSyntax.mk h))
        interleaveForks h' t
    | .nil => pure prog

def MultithreadHEffectProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        []
        [⟨"MultithreadHEffect",fun heff cmd fork rec => do
            let forks ← unfoldFork fork
            match forks with
            | .some v => do
                v.forM (fun z => logInfo <| toMessageData z)
                let evals ← v.toList.mapM (rec true #[])
                --let evals : Array (TSyntax `term) := evals.map (TSyntax.mk)
                --`("catchEff " ++ toString $(List.length v[ $evals,* ]))
                let vLen := toString (v.size)
                let zz ← `(basicStep <| "forkThreads" ++ $(Syntax.mkStrLit vLen))
                match evals with
                | .cons h t => interleaveForks h t
                | .nil => pure zz
            | .none => `(basicStep "noforks?")⟩]
        []

end MultithreadHEffect
