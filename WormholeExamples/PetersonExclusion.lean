/-
 Example of Peterson's exclusions algorithm, using some shared state between threads to
 provide fair access to a critical section.
-/

import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM
import FreerWormhole.Effects.LabelEffect
import FreerWormhole.Effects.SignaledStateEffect
import FreerWormhole.Effects.MultithreadHEffect

import FreerWormhole.Wormhole
import FreerWormhole.MetaProgramGraph
import FreerWormhole.ForeverLoop

import SolifugidZ.LTL
import SolifugidZ.CTL

open EffM HEffM Effect HEffect
open LabelEffect SignaledStateEffect IOEffect MultithreadHEffect
open Wormhole ProgramGraph MetaProgramGraph ForeverLoop
open CTL

structure SharedVariables : Type where
    (lock₁ lock₂ : Bool)
    (next : Fin 2)
    deriving BEq

def strLock : Bool → String
| .true => "o"
| .false => "⬝"

def StateToAP (st : SharedVariables) : List String :=
    List.filterMap id
        [
            if st.lock₁ then .some "lock1" else .none,
            if st.lock₂ then .some "lock2" else .none,
            if st.next.val == 0 then .some "next0" else .some "next1"
        ]

instance : ToString SharedVariables where
    toString s := "|" ++ strLock s.lock₁ ++ strLock s.lock₂ ++ toString s.next.val ++ "|"

instance : Ord SharedVariables where
    compare := fun s₁ s₂ =>
        match compare s₁.lock₁ s₂.lock₁ with
        | .lt => .lt
        | .gt => .gt
        | .eq => match compare s₁.lock₂ s₂.lock₂ with
                 | .lt => .lt
                 | .gt => .gt
                 | .eq => compare s₁.next s₂.next

instance : StateCardinality SharedVariables where
    sSize := 8
    genState := fun (n : Fin 8) =>
        let next : Fin 2 := if n.val < 4 then Fin.mk 0 (by simp) else Fin.mk 1 (by simp)
        let l1 := if n.val % 2 == 0 then false else true
        let l2 := if (n.val/2) % 2 == 0 then false else true
        {lock₁ := l1, lock₂ := l2, next := next}
    

defHEffectful process1 [[MultithreadHEffect !! SignaledStateEffect SharedVariables, LabelEffect, IOEffect]]
    >| Unit :=
    foreverLoop <| do
        labelBlock "wait1" <| do
            modifyState <| fun (s : SharedVariables) => { s with lock₁ := true, next := ⟨1, by simp⟩}
            liftIO <| IO.println "wait1"
            let _ ← waitFor <| fun (s : SharedVariables) => s.lock₂ != true || s.next.val != 1
        labelBlock "crit1" <| do
            liftIO <| IO.println "crit1"
            liftIO <| IO.sleep 500
        modifyState <| fun (s : SharedVariables) => { s with lock₁ := false}

defHEffectful process2 [[MultithreadHEffect !! SignaledStateEffect SharedVariables, LabelEffect, IOEffect]]
    >| Unit :=
    foreverLoop <| do
        labelBlock "wait2" <| do
            liftIO <| IO.println "wait2"
            modifyState <| fun (s : SharedVariables) => { s with lock₂ := true, next := ⟨0, by simp⟩}
            let _ ← waitFor <| fun (s : SharedVariables) => s.lock₁ != true || s.next.val != 0
        labelBlock "crit2" <| do
            liftIO <| IO.println "crit2"
            liftIO <| IO.sleep 50
        modifyState <| fun (s : SharedVariables) => { s with lock₂ := false}


defHEffectful startAndFork [[MultithreadHEffect  !! SignaledStateEffect SharedVariables, LabelEffect, IOEffect]]
    >| Unit := do
    label "fork"
    forkThreads [process1, process2]

def interpreter (mtx : IO.Mutex SharedVariables) (cv : IO.Condvar)
    : EffM [SignaledStateEffect SharedVariables, LabelEffect, IOEffect] PUnit → IO Unit := fun p =>
    runIO <| runLabelEffect <| runSignaledStateMutex mtx cv <| p


def elaborator (mtx : IO.Mutex SharedVariables) (cv : IO.Condvar)
    : Elaboration [MultithreadHEffect, (hLifted (SignaledStateEffect SharedVariables)), hLifted LabelEffect, hLifted IOEffect]
                  [SignaledStateEffect SharedVariables, LabelEffect, IOEffect] :=
    elabMultithread (interpreter mtx cv)
    <| elabEff (SignaledStateEffect SharedVariables)
    <| elabEff LabelEffect
    <| elabLast IOEffect


def main : IO Unit := do
    IO.println s!"Hello, argh!"
    let mtx ← IO.Mutex.new { lock₁ := false, lock₂ := false, next := ⟨0,by simp⟩}
    let cv ← IO.Condvar.new
    let _ ← interpreter mtx cv <| elaborate (elaborator mtx cv) startAndFork
    pure ()


open Lean Elab Expr Command Meta Term Wormhole MetaProgramGraph


genWormhole2 genPG >: buildProgramGraphWormhole
    [
        IOEffectProgramGraphProcessor,
        LabelEffectProgramGraphProcessor,
        SignaledStateEffectProgramGraphProcessor,
        MultithreadHEffectProgramGraphProcessor,
        ForeverLoopProgramGraphProcessor
    ]
    -- pure processor
    programGraphPure
    :<

def zedB : ProgramGraphBuilderT Id (MetaProgramGraph Nat String SharedVariables) := goWormhole2 (startAndFork : HEffM [MultithreadHEffect, (hLifted (SignaledStateEffect SharedVariables)), hLifted LabelEffect, hLifted IOEffect] PUnit)
def zed1 : ProgramGraphBuilderT Id (MetaProgramGraph Nat String SharedVariables) := goWormhole2 (process1 : HEffM [MultithreadHEffect, (hLifted (SignaledStateEffect SharedVariables)), hLifted LabelEffect, hLifted IOEffect] PUnit)
def zed2 : ProgramGraphBuilderT Id (MetaProgramGraph Nat String SharedVariables) := goWormhole2 (process2 : HEffM [MultithreadHEffect, (hLifted (SignaledStateEffect SharedVariables)), hLifted LabelEffect, hLifted IOEffect] PUnit)
def zed := ProgramGraphBuilderT.build (zedB >>= addTerminalNode "finish")

#check zed
#widget VizGraph.vizGraph toVizProgram zed
#widget VizGraph.vizGraph toVizUnfoldedProgram zed StateToAP ["wait1","wait2","crit1","crit2","finish"]

def zedFSM : FSM Nat (APBits ["wait1","wait2","crit1","crit2","finish"]) String :=
    toFSM zed [SharedVariables.mk false false ⟨0,by simp⟩] StateToAP ["wait1","wait2","crit1","crit2","finish"]


--#eval checkUsingCTL zedFSM [ctl ∀□¬(<+"crit1"+> ∧ <+"crit2"+>)]
--#eval checkUsingCTL zedFSM [ctl ∀◇<+"wait1"+>]
--#eval checkUsingCTL zedFSM [ctl ∀□∃◇<+"finish"+>]
--#eval checkUsingCTL zedFSM [ctl ∀◇<+"wait1"+>∨<+"wait2"+>]
--#eval checkUsingCTL zedFSM [ctl ∀□(<+"wait1"+> → ∀◇<+"crit1"+>)]
#eval checkUsingCTL zedFSM [ctl ∀□¬(<+"crit1"+> ∧ <+"crit2"+>)]

--#widget VizGraph.vizGraph (toJson <| VizGraph.vizLTLTest zedFSM [ [ltl □◇<+"wait1"+> → □◇<+"crit1"+>], [ltl □¬(<+"crit1"+> ∧ <+"crit2"+>)], [ltl ◇<+"wait1"+>] ])

