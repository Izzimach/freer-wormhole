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

import FreerWormhole.Effects.Freer
--import FreerWormhole.Effects.HEff
import FreerWormhole.Effects.StdEffs
import FreerWormhole.Wormhole

open Lean Elab Command Term Meta PrettyPrinter

open Freer Effect StdEffs Wormhole

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
    (flowOut : List (Action × Location))
    (jumpTo : RBMap String (List (Action × Nat)) compare)

namespace MetaProgramGraph

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
    let newTransitions := p₁.flowOut.map (fun ⟨a,l₁⟩ => ⟨l₁,p₂.flowIn.map (fun l₂ => ProgramTransition.mk .none a id l₂)⟩)
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

def ProgramGraphBuilderT.build : ProgramGraphBuilderT Id a → a := fun b =>
    @StateT.run' ProgramGraphBuilderContext Id _ _ b {nextLocValue := 0}

def nextLoc {m : Type → Type} [Monad m] : ProgramGraphBuilderT m Nat :=
    StateT.modifyGet (fun c => ⟨c.nextLocValue,{ c with nextLocValue := c.nextLocValue + 1}⟩)

instance [Monad m] : Monad (ProgramGraphBuilderT m) where
    bind := fun m f => StateT.bind m f
    pure := StateT.pure

instance [Functor m] [Monad m] : Functor (ProgramGraphBuilderT m) where
    map := fun f p => StateT.map f p


def basicStep {S : Type} (a : Action) [Ord Action] [Inhabited Action] [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let l₁ ← nextLoc
    pure {
        toProgramGraph := {
          transitions := .empty,
          locationLabels := .empty,
          starts := [l₁]
        },
        flowIn := [l₁],
        flowOut := [⟨a, l₁⟩],
        jumpTo := .empty
    }

def stateModStep {S : Type} (a : Action) (f : S → S) [Ord Action] [Inhabited Action] [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let l₁ ← nextLoc
    let l₂ ← nextLoc 
    pure {
        toProgramGraph := {
          transitions := RBMap.fromList [⟨l₁,[ProgramTransition.mk .none a f l₂]⟩] compare,
          locationLabels := .empty,
          starts := [l₁]
        },
        flowIn := [l₁],
        flowOut := [⟨default, l₂⟩],
        jumpTo := .empty
    }

def sequenceProgramGraphs [Ord Act] [Inhabited Act] [Monad m]
    (b₁ b₂ : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables))
    :  ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    let p₁ ← b₁
    let p₂ ← b₂
    pure (sequencePrograms p₁ p₂)

/-
 Generic branch builder. Produces a nondeterministic branch. For a branch with guards using
 the StateVariables, use stateIf from the StateModelHEff higher-order effect.
 For each branch, pass in:
  - guard
  - state update
  - ProgramGraph
-/
def branchProgramGraph {Act StateVariables : Type} [Ord Act] [Inhabited Act] [Monad m]
  (test₁ : StateVariables → Bool)
  (action₁ : Act)
  (modify₁ : StateVariables → StateVariables)
  (prog₁ : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) )
  (test₂ : StateVariables → Bool)
  (action₂ : Act)
  (modify₂ : StateVariables → StateVariables)
  (prog₂ : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) )
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    let prog₁ ← prog₁ 
    let prog₂ ← prog₂
    let ifLoc ← nextLoc
    let ifEnd ← nextLoc
    -- Connect the ifLoc to the inflows of the two programs. We use guards here
    -- based on the test function that was passed in.
    let transitionsIn₁ := prog₁.flowIn.map (fun l => ⟨ifLoc,ProgramTransition.mk (.some test₁) action₁ modify₁ l⟩)
    let transitionsIn₂ := prog₂.flowIn.map (fun l => ⟨ifLoc,ProgramTransition.mk (.some test₂) action₂ modify₂ l⟩)
    -- Connect outflows of the two programs to the ifEnd. No guards or state change, but do use
    -- the action labels of the flowOut of each ProgramGraph
    let transitionsOut₁ := prog₁.flowOut.map (fun ⟨a,l⟩ => ⟨l,ProgramTransition.mk .none a id ifEnd⟩)
    let transitionsOut₂ := prog₂.flowOut.map (fun ⟨a,l⟩ => ⟨l,ProgramTransition.mk .none a id ifEnd⟩)
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
        flowOut := [⟨default,ifEnd⟩],
        jumpTo := mergeRBMaps prog₁.jumpTo prog₂.jumpTo
    }

def jump {S : Type} (jumpTargetId : String) [Ord Action] [Inhabited Action] [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let l ← nextLoc
    pure {
        toProgramGraph := {
          transitions := .empty,
          locationLabels := .empty,
          starts := [l]
        },
        flowIn := [l],
        flowOut := [],
        jumpTo := RBMap.fromList [⟨jumpTargetId,[⟨default,l⟩]⟩] compare
    }

/-
 Handle recursion
 
 Any recursive calls are indicated by a jumpTo with a given
 ID; all these transitions are re-routed to lead to the automata start node(s) and removed from the
 exoTransitions set. You can give these recursive edges a label (or use "" for no label).
-/
def resolveRecursiveJump {S : Type} [Ord Action] [Inhabited Action] [Monad m]
    (p : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S)) (jumpId : String) 
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let p ← p
    -- find recursive calls, if any. Also remove them from the jumpTo set
    let ⟨recursions, jumpTo⟩ :=
        match p.jumpTo.find? jumpId with
        | .none => Prod.mk [] p.jumpTo
        | .some r => Prod.mk r (p.jumpTo.erase jumpId)
    -- add transitions from recursion to the flowIn nodes
    let newTransitions := 
        RBMap.fromList
            (recursions.map (fun ⟨a,l₁⟩ => ⟨l₁,p.flowIn.map (fun l₂ => ProgramTransition.mk .none a id l₂)⟩))
            compare
    pure { p with
        transitions := mergeRBMaps p.transitions newTransitions,
        jumpTo := jumpTo
    }

/-
 While building a ProgramGraph we store flowIn/flowOut edges that don't lead to an actualy node, and will
 get filled in later. This is to reduce the amount of redundant nodes. However when  vizualizing these
 flows don't show up. So this function will add nodes to server as source/sink for those flow edges.
-/
def reifyFlows {Act StateVariables : Type} [Ord Act] [Inhabited Act] [Monad m] [Inhabited StateVariables]
    (pg : MetaProgramGraph Nat Act StateVariables)
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    let inNode ← nextLoc
    let outNode ← nextLoc 
    let inTransitions := 
        if pg.flowIn.length == 0
        then []
        else [⟨inNode,pg.flowIn.map (fun l => ProgramTransition.mk .none default id l)⟩]
    let outTransitions := pg.flowOut.map (fun ⟨a,l⟩ => ⟨l,[ProgramTransition.mk .none a id outNode]⟩)
    let allTransitions := mergeRBMaps pg.transitions (RBMap.fromList (inTransitions ++ outTransitions) compare)
    pure {
        toProgramGraph := {
          transitions := allTransitions,
          starts := if pg.flowIn.length == 0
                    then pg.starts
                    else [inNode],
          locationLabels := pg.locationLabels
        },
        flowIn := [],
        flowOut := [],
        jumpTo := pg.jumpTo
    }


inductive ProgramLabelCommand : Type u where
    | Label : String → ProgramLabelCommand

-- an effect that labels a node of the generated automata
def ProgramLabel : Effect :=
    {
        op := ProgramLabelCommand,
        ret := fun _ => Unit
    }

def label [HasEffect ProgramLabel effs] (l : String) : Freer effs PUnit :=
    @send ProgramLabel effs _ (ProgramLabelCommand.Label l)


def const {a b : Type} (c : b) : a → b := fun _ => c

def cTrue {a : Type} : a → Bool := const true
def cFalse {a : Type} : a → Bool  := const false

def monadFuncs
    (cmdTransform : Expr → Expr → TermElabM Syntax) 
    (pureTransform : Expr → TermElabM Syntax) : 
        RBMap String TransformerAppSyntax compare :=
    RBMap.ofList
    [
        ⟨"send", fun args mk => do
            let eff := args.get! 0
            let op := args.get! 3
            cmdTransform eff op
        ⟩,
        ⟨"bind", fun args mk => do
            let a₁ := args.get! 4
            let a₂ := args.get! 5
            let r₁ ← mk true #[] a₁
            let r₂ ← mk true #[mkStrLit "bad argument"] a₂
            `(sequenceProgramGraphs $(TSyntax.mk r₁) $(TSyntax.mk r₂))
        ⟩,
        ⟨"Pure", fun args mk => do
            let a := args.get! 2
            pureTransform a
        ⟩,
        ⟨"pure", fun args mk => do
            let a := args.get! 3
            pureTransform a
        ⟩,
        -- if
        ⟨"ite", fun args mk => do
            logInfo <| args.get! 0
            let b₁ ← mk true args (args.get! 3)
            let b₂ ← mk true args (args.get! 4)
            `(branchProgramGraph cTrue default id $(TSyntax.mk b₁) cTrue default id $(TSyntax.mk b₂))
        ⟩,
        -- decidible if
        ⟨"dite", fun args mk => do
            let b₁ ← mk true args (args.get! 3)
            let b₂ ← mk true args (args.get! 4)
            `(branchProgramGraph cTrue default id $(TSyntax.mk b₁) cTrue default id $(TSyntax.mk b₂))
        ⟩,
        -- A recursive call
        ⟨"jump", fun args mk => do
            match args.get! 0 with
            | .lit (.strVal s) => `(jump $(Syntax.mkStrLit s))
            | _ => `("Error: bad recurse id")
        ⟩,
        -- Wrapper around a recursive function
        ⟨"fix", fun args mk => do
            let recVar ← mkFreshExprMVar (mkConst ``String)
            let recId := recVar.mvarId!.name.toString
            recVar.mvarId!.assign (mkStrLit recId)
            let recFun := args.get! 4
            let recursiveCall := mkAppN (mkConst ``jump) #[recVar]
            let recurseBody ← mk true #[mkStrLit "arg", recursiveCall] recFun
            `(resolveRecursiveJump $(TSyntax.mk recurseBody) $(Syntax.mkStrLit recId))
        ⟩
    ]


--
-- when processing an effect, we can work directly with the Expr but it's usually better to
-- just return Syntax
--

def ProcessEffects := List (String × TermElabM Syntax)

/- If the state monad represents the actual state used in the program graph, we can
   use this Processor. -/
def StateProcessor : TermElabM Syntax :=
    `(fun (op : Type 1) (c : StateOp _) =>
          match c with
          | StateOp.Put s => stateModStep "[[put]]" (fun _ => s)
          | StateOp.Get => basicStep "[[get]]"
          | StateOp.Modify f => stateModStep "[[modify]]" f)

def exampleProcessors : ProcessEffects :=
    [
        ⟨"NoopEffect", `(fun (op : Type 1) (x : op) => basicStep "Noop")⟩,
        ⟨"IOEffect", `(fun (op : Type 1) (o : StdEffs.IOX) => basicStep "IO")⟩,
        ⟨"ProgramLabel", `(fun (op : Type 1) (x : ProgramLabelCommand) => basicStep ("[[" ++ x.1 ++ "]]"))⟩,
        ⟨"StateEff", StateProcessor⟩
    ]

-- given some processors to process different effects (ProcessEffects) this will
-- look at the effect and operator passed in and try to apply the appropriate
-- processor.
def processOps : ProcessEffects → Expr → Expr → TermElabM Syntax := fun pr eff op => do
    match eff.getAppFn with
    | .const effName lvls => do
        let eNameEnd := effName.components.getLastD "_"
        match List.lookup eNameEnd.toString pr with
        | .some fm => do
            withFreshMacroScope <| do
                let et ← inferType op
                let etStx ← `(?et)
                let opStx ← `(?op)
                let etVar ← elabTerm etStx .none
                let opVar ← elabTerm opStx (.some et)
                etVar.mvarId!.assign et
                opVar.mvarId!.assign op
                let f ← fm
                let declName := (←read).declName?
                match declName with
                | .some d => logInfo ("decl: " ++ d)
                | .none => logInfo "NO DECL"
                `($(TSyntax.mk f) ?et ?op)
        | .none => `("no handler for effect " ++ $(Syntax.mkStrLit effName.toString))
    | _ => `("malformed effect")

def processPure : Expr → TermElabM Syntax :=
    fun e => `(basicStep ("pure"))




-- final monad implementing the state and IO
--genWormhole2 genFSM >: monadFuncs (processOps exampleProcessors) processPure :<



def toFSM (p : MetaProgramGraph Nat String StateVariables) (initialStates : List StateVariables)
    [ToString StateVariables] [BEq StateVariables] [Ord StateVariables] [StateCardinality StateVariables]
    : FSM Nat (List String) String :=
    FSM.compactFSM <|
        unfoldProgramGraph
            p.toProgramGraph
            (fun l s xs => [toString l ++ "-" ++ toString s])
            id
            initialStates


def toVizAutomata (a : FSM Nat (List String) String) : Json :=
    toJson <|
        VizGraph.toVizFSM
            (FSM.onlyReachableFSM <| a)
            (fun vl => String.intercalate "/" vl)
            id
            "/start"
            "/end"

def toVizProgram (p : MetaProgramGraph Nat String Bool) : Json :=
    toJson <| VizGraph.toVizProgramGraph p.toProgramGraph id

/-
def dumpArgh [HasEffect IOEffect m] : Freer m Nat := do
    ioEff (IO.println "argh")
    pure 4

def if3 [HasEffect ProgramLabel m] [HasEffect (StateEff Bool) m] [HasEffect IOEffect m] : Nat →  Freer m Nat :=
    fun z => do
        put true
        if z = 0
        then dumpArgh
        else do
            put false
            ioEff (IO.println "step")
            label "looping"
            if3 (z-1)

def wormHoleX : Freer [ProgramLabel, StateEff Bool, IOEffect] Nat := do
    label "start"
    let y ← if3 3
    let z : Bool ← @get Bool _ _
    if z
    then label "mid"
    else do
        label "false"
        put false
    label "end"
    pure y

def x := toVizProgram <| ProgramGraphBuilderT.build (goWormhole2 wormHoleX)
def xf := toVizAutomata <| toFSM (ProgramGraphBuilderT.build (goWormhole2 wormHoleX)) [default]
#widget VizGraph.vizGraph xf


def twoSteps {m : Type → Type} [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat String Bool) := do
    let p₁ ← basicStep "a"
    let p₂ ← basicStep "b"
    --branchProgramGraph id  "true" id p₁ not "false" id p₂
    pure <| sequencePrograms p₁ p₂


def prog := Id.run <| ProgramGraphBuilderT.run' (twoSteps >>= reifyFlows) { nextLocValue := 1 }

#eval toJson <| toVizProgram prog
#widget VizGraph.vizGraph (toVizAutomata <| toFSM prog)
#widget VizGraph.vizGraph (toVizProgram prog)
-/

end MetaProgramGraph
