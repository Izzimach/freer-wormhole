/-
 Example of Peterson's exclusions algorithm, using some shared state between threads to
 provide fair access to a critical section.
-/

import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.StdEffs

open Freer Effect HEffect StdEffs StdHEffs




inductive ProgramLabelCommand : Type u where
    | Label : String → ProgramLabelCommand

-- an effect that labels a node of the generated automata
def ProgramLabel : Effect :=
    {
        op := ProgramLabelCommand,
        ret := fun _ => Unit
    }

def programLabelHandler {a : Type} : Handler a a ProgramLabel effs PUnit :=
    {
        ret := fun a _ => Freer.Pure a,
        handle := fun ou next _ =>
            match ou with
            | .Leaf l => next PUnit.unit PUnit.unit
            | .Node ou' => .Impure ou' (fun x => next x PUnit.unit)
    }

def runProgramLabel {effs : List Effect} : Freer (ProgramLabel :: effs) x → Freer effs x :=
    fun m => handleFreer (@programLabelHandler effs x) m PUnit.unit

def label [HasHEffect (hLifted ProgramLabel) heffs] (l : String) : Hefty heffs PUnit :=
    @hLift ProgramLabel heffs _ (ProgramLabelCommand.Label l)


structure SharedVariables : Type where
    (lock₁ lock₂ : Bool)
    (next : Fin 2)

def process1 
    [HasHEffect (hLifted (SignalStateEff SharedVariables)) heffs]
    [HasHEffect (hLifted ProgramLabel) heffs]
    [HasHEffect (hLifted IOEffect) heffs]
    (countdown : Nat) : Hefty heffs Unit := do
        let _ ← ssModifyH <| (fun (s : SharedVariables) => ⟨(),{ s with lock₁ := true, next := ⟨1, by simp⟩}⟩)
        label "wait process 1"
        let p ← ssWaitH (fun (s : SharedVariables) => s.lock₂ != true || s.next.val != 1) id
        label "critical section 1"
        ioEffH <| IO.println s!"value 1: {p.next}"
        ioEffH <| IO.sleep 500
        let _ ← ssModifyH <| (fun (s : SharedVariables) => ⟨(), { s with lock₁ := false}⟩)
        if countdown > 0
        then process1 (countdown-1)
        else pure ()

def process2
    [HasHEffect (hLifted (SignalStateEff SharedVariables)) heffs]
    [HasHEffect (hLifted ProgramLabel) heffs]
    [HasHEffect (hLifted IOEffect) heffs]
    (countdown : Nat) : Hefty heffs Unit := do
        let _ ← ssModifyH <| (fun (s : SharedVariables) => ⟨(),{ s with lock₂ := true, next := ⟨0, by simp⟩}⟩)
        let p ← ssWaitH (fun (s : SharedVariables) => s.lock₁ != true || s.next.val != 0) id
        ioEffH <| IO.println s!"value 2: {p.next}"
        ioEffH <| IO.sleep 50
        let _ ← ssModifyH <| (fun (s : SharedVariables) => ⟨(),{ s with lock₂ := false}⟩)
        if countdown > 0
        then process2 (countdown-1)
        else pure ()


def startAndFork 
    [HasHEffect (AtomicStateHEff SharedVariables) heffs]
    [HasHEffect (hLifted (SignalStateEff SharedVariables)) heffs]
    [HasHEffect (hLifted ProgramLabel) heffs]
    [HasHEffect (hLifted IOEffect) heffs]
    : Hefty heffs Unit := do
    @atomicFork SharedVariables _ _ [process1 10, process2 8]

def interpreter
    (mtx : IO.Mutex SharedVariables)
    (cv : IO.Condvar)
    : Freer [SignalStateEff SharedVariables, ProgramLabel, IOEffect] PUnit → IO Unit := fun p =>
    runIOEff <| runProgramLabel <| runSignalStateMutex mtx cv p


def elaborator (mtx : IO.Mutex SharedVariables) (cv : IO.Condvar)
    : Elaboration [AtomicStateHEff SharedVariables, (hLifted (SignalStateEff SharedVariables)), hLifted ProgramLabel, hLifted IOEffect]
                  [SignalStateEff SharedVariables, ProgramLabel, IOEffect] :=
    elabAtomicState (interpreter mtx cv)
    <| elabEff (SignalStateEff SharedVariables)
    <| elabEff ProgramLabel
    <| elabLast IOEffect


def main : IO Unit := do
    IO.println s!"Hello, argh!"
    let mtx ← IO.Mutex.new { lock₁ := false, lock₂ := false, next := ⟨0,by simp⟩}
    let cv ← IO.Condvar.new
    let _ ← interpreter mtx cv <| elaborate (elaborator mtx cv) startAndFork
    pure ()
  
