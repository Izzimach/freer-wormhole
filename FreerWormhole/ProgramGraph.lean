--
-- Use wormhole to generate a Program Graph from monadic code. This is then
-- (optionally) combined with other Program Graphs and unfolded into
-- a transition system for model checking
--

import Lean
import SolifugidZ.Basic
import SolifugidZ.ProgramGraph
import SolifugidZ.FSM
import SolifugidZ.VizGraph

open Lean Elab Command Term Meta PrettyPrinter

open Basic ProgramGraph

/-
 We augment the standard ProgramGraph with some extra data:
 - flowIn and flowOut support connecting together two ProgramGraphs. The flowOut nodes of one
   ProgramGraph connect to flowIn nodes of the successor ProgramGraph. Edges use the Action label
   provided in flowOut
 - jumpTo productes transitions to another location which may not (yet) be contained in the ProgramGraph.
   This is used to implement recursion/looping and exception handling.
-/ 
structure MetaProgramGraph (Location : Type) (Action : Type) (StateVariables : Type) [Ord Location] [Ord Action]
    extends ProgramGraph Location Action StateVariables where
    (flowIn : List Location)
    (flowOut : Action × List Location)
    (jumpTo : RBMap Location (List (Action × Location)) compare)

def mergeRBMaps [Ord Loc] :
    {Z : Type} → RBMap Loc (List Z) compare
               → RBMap Loc (List Z) compare
               → RBMap Loc (List Z) compare
        := fun m₁ m₂ => RBMap.mergeBy (fun k v₁ v₂ => v₁ ++ v₂) m₁ m₂

/-
 Connect two ProgramGraphs so that one ProgramGraph flows into the other.
 Note that this is different than sequencing two FSMs in that the
 locations are not renumbered or modified. You need to make sure the locations of the
 two ProgramGraphs are disjoint.
-/
def sequencePrograms {Loc Act StateVariables : Type} [Ord Loc] [Ord Act] [Inhabited Act]
    (p₁ p₂ : MetaProgramGraph Loc Act StateVariables) : MetaProgramGraph Loc Act StateVariables :=
    let pg₁ := p₁.toProgramGraph
    let pg₂ := p₂.toProgramGraph
    -- we add the same set of transitions to all flowOuts of p₁
    let fromFlowOuts : List (ProgramTransition Loc Act StateVariables) := p₂.flowIn.map (fun l => ⟨.none,p₁.flowOut.1,id,l⟩)
    let newTransitions := p₁.flowOut.2.map (fun loc => ⟨loc,fromFlowOuts⟩)
    {
      toProgramGraph :=
        {
            transitions := mergeRBMaps (mergeRBMaps pg₁.transitions pg₂.transitions) (RBMap.fromList newTransitions compare),
            locationLabels := mergeRBMaps pg₁.locationLabels pg₂.locationLabels,
            starts := pg₁.starts
        },
      flowIn := p₁.flowIn,
      flowOut := p₂.flowOut,
      jumpTo := mergeRBMaps p₁.jumpTo p₂.jumpTo
    }


structure ProgramGraphBuilderContext where
    (nextLocValue : Nat)
    
def ProgramGraphBuilderT : (m : Type → Type) → Type → Type := StateT ProgramGraphBuilderContext

def ProgramGraphBuilderT.run' := @StateT.run'

def nextLoc {m : Type → Type} [Monad m] : ProgramGraphBuilderT m Nat :=
    StateT.modifyGet (fun c => ⟨c.nextLocValue,{ c with nextLocValue := c.nextLocValue + 1}⟩)

instance [Monad m] : Monad (ProgramGraphBuilderT m) where
    bind := fun m f => StateT.bind m f
    pure := StateT.pure


def basicStep (a : Action) [Ord Action] [Inhabited Action] [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat Action Bool) := do
    let l₁ ← nextLoc
    pure {
        toProgramGraph := {
          transitions := .empty,
          locationLabels := .empty,
          starts := [⟨l₁,false⟩]
        },
        flowIn := [l₁],
        flowOut := ⟨a, [l₁]⟩,
        jumpTo := .empty
    }


--
-- Generic branch builder. For each branch, pass in:
--  - guard
--  - state update
--  - ProgramGraph
--
def branchProgramGraph {Act StateVariables : Type} [Ord Act] [Inhabited Act] [Monad m]
  (test₁ : StateVariables → Bool)
  (modify₁ : StateVariables → StateVariables)
  (prog₁ : MetaProgramGraph Nat Act StateVariables)
  (test₂ : StateVariables → Bool)
  (modify₂ : StateVariables → StateVariables)
  (prog₂ : MetaProgramGraph Nat Act StateVariables)
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    let ifLoc ← nextLoc
    let ifEnd ← nextLoc
    -- Connect the ifLoc to the inflows of the two programs. We use guards here
    -- based on the test function that was passed in.
    let transitionsIn₁ := prog₁.flowIn.map (fun l => ⟨ifLoc,ProgramTransition.mk (.some test₁) default modify₁ l⟩)
    let transitionsIn₂ := prog₂.flowIn.map (fun l => ⟨ifLoc,ProgramTransition.mk (.some test₂) default modify₂ l⟩)
    -- Connect outflows of the two programs to the ifEnd. No guards or state change, but do use
    -- the action labels of the flowOut of each ProgramGraph
    let transitionsOut₁ := prog₁.flowOut.2.map (fun l => ⟨l,ProgramTransition.mk .none prog₁.flowOut.1 id ifEnd⟩)
    let transitionsOut₂ := prog₂.flowOut.2.map (fun l => ⟨l,ProgramTransition.mk .none prog₂.flowOut.1 id ifEnd⟩)
    let extraTransitions : List (Nat × ProgramTransition Nat Act StateVariables):= List.join [transitionsIn₁,transitionsIn₂, transitionsOut₁, transitionsOut₂]
    let originalTransitions := mergeRBMaps prog₁.transitions prog₂.transitions
    let allTransitions := extraTransitions.foldl
        (fun m ⟨loc,tra⟩ => match m.find? loc with
                            | .none => m.insert loc [tra]
                            | .some tras => m.insert loc (tra :: tras))
        originalTransitions
    pure {
        toProgramGraph := {
          transitions := allTransitions,
          starts := [],
          locationLabels := mergeRBMaps prog₁.locationLabels prog₂.locationLabels
        },
        flowIn := [ifLoc],
        flowOut := ⟨default,[ifEnd]⟩,
        jumpTo := mergeRBMaps prog₁.jumpTo prog₂.jumpTo
    }


/-
 If/then/else setup of ProgramGraphs. The test function returns a new (possibly unmodified) state s and
 and a boolean value, so (s → (s × Bool)). The value of the Bool determines which of two ProgramGraphs are run.
-/
def ifThenElse {Act StateVariables : Type} [Ord Act] [Inhabited Act] [Monad m]
  (test : StateVariables → (StateVariables × Bool))
  (pThen pElse : MetaProgramGraph Nat Act StateVariables)
  : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) :=
    branchProgramGraph
        (Prod.snd ∘ test)
        (Prod.fst ∘ test)
        pThen
        (not ∘ Prod.snd ∘ test)
        (Prod.fst ∘ test)
        pElse

def twoSteps {m : Type → Type} [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat String Bool) := do
    let p₁ ← basicStep "a"
    let p₂ ← basicStep "b"
    --ifThenElse (fun s => ⟨s,s⟩) p₁ p₂
    pure p₁
    
def toFSM (p : MetaProgramGraph Nat String StateVariables) [ToString StateVariables] [BEq StateVariables] [Ord StateVariables] [StateCardinality StateVariables]
    : FSM Nat (List String) String :=
    FSM.compactFSM <|
        unfoldProgramGraph
            p.toProgramGraph
            (fun l s xs => [toString l ++ "-" ++ toString s])
            id


def prog := Id.run <| ProgramGraphBuilderT.run' twoSteps { nextLocValue := 0 }

def toVizAutomata (a : FSM Nat (List String) String) : Json :=
    toJson <|
        VizGraph.toVizFSM
            (FSM.onlyReachableFSM <| a)
            (fun vl => String.intercalate "/" vl)
            id
            "/start"
            "/end"

#eval toJson <| toVizAutomata <| toFSM prog
#widget VizGraph.vizGraph (toJson <| toVizAutomata <| toFSM prog)
