/-
 Example of Peterson's exclusions algorithm, using some shared state between threads to
 provide fair access to a critical section.
-/

import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.StdEffs

import FreerWormhole.Wormhole
import FreerWormhole.Automata

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
        --ioEffH <| IO.println s!"value 1: {p.next}"
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
        --ioEffH <| IO.println s!"value 2: {p.next}"
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
    --@atomicIf SharedVariables _ heffs _ (fun s => ⟨s.lock₁ == true, s⟩) (hPure ()) (hPure ())
    label "fork"
    @atomicFork SharedVariables _ _ [process1 10, process2 8]
    @atomicIf SharedVariables _ heffs _ (fun s => ⟨s.lock₁ == true, s⟩) (hPure ()) (hPure ())

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


open Lean Elab Expr Command Meta Term Wormhole ProgramAutomata


def petersonProcessors : ProcessEffects :=
    
    [
        ⟨"NoopEffect", `(fun (op : Type 1) (x : op) => zeroNode)⟩,
        ⟨"IOEffect", `(fun (op : Type 1) (o : StdEffs.IOX) => labeledNode "IO!")⟩,
        ⟨"AutomataLabel", `(fun (op : Type 1) (x : VertexLabelCommand) => labeledNode x.1)⟩,
        ⟨"SignalStateEff", `(fun (op : Type 1) (x : op) => labeledNode "SignalState")⟩,
        ⟨"ProgramLabel", `(fun (op : Type 1) (x : op) => labeledNode "Label")⟩,
        ⟨"AtomicStateHEff", `(fun (op : Type 2) (x : AtomicStateHEff SharedVariables) => labelNode "atomic")⟩
    ]

def processHE2 : List (String × ProcessHEff) := 
    [
        ⟨"AtomicStateHEff", fun heff cmd fork rc => do
            let forks ← unfoldFork fork
            match forks with
            | .some v => do
                if v.size == 0
                then `(labeledNode "AtomicStateHeff")
                else do
                    --let evals ← v.mapM (rc true #[])
                    --logInfo <| toString v.size
                    let v : Array Syntax ← v.mapM (fun x => rc true #[] x)
                    -- need to extend this to properly handle branches that are ≠ 2
                    let v₁ : Syntax := v.getD 0 (Syntax.mkStrLit "branch error 0")
                    let v₂ : Syntax := v.getD 1 (Syntax.mkStrLit "branch error 1")
                    `(branchAutomata $(TSyntax.mk v₁) $(TSyntax.mk v₂))
            | .none => `("error")⟩
    ]


#check GetElem.getElem
genWormhole2 genFSM >: heffFuncs (processOps petersonProcessors) (heffX processHE2) processPure :<

def zed := goWormhole2 (startAndFork : Hefty [AtomicStateHEff SharedVariables, (hLifted (SignalStateEff SharedVariables)), hLifted ProgramLabel, hLifted IOEffect] PUnit)

#check zed
#widget VizGraph.vizGraph toVizAutomata zed

