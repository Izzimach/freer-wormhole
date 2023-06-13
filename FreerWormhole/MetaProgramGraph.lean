--
-- Use wormhole to generate a Program Graph from monadic code. This is then
-- (optionally) combined with other Program Graphs and unfolded into
-- a transition system for model checking
--

import Lean

import SolifugidZ.Basic
import SolifugidZ.ProgramGraph
import SolifugidZ.APBits
import SolifugidZ.FSM
import SolifugidZ.VizGraph

import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole

open Lean Elab Command Term Meta PrettyPrinter

open EffM Effect HEffM HEffect Wormhole

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
    -- each flowOut of p₁ gets a transition to every flowIn of p₂
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

def labelStep {S : Type} (l : String) [Ord Action] [Inhabited Action] [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let l₁ ← nextLoc
    pure {
        toProgramGraph := {
          transitions := .empty,
          locationLabels := RBMap.fromList [⟨l₁,[l]⟩] compare,
          starts := [l₁]
        },
        flowIn := [l₁],
        flowOut := [⟨default, l₁⟩],
        jumpTo := .empty
    }


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

def singleStep {S : Type} (a : Action) (guard : S → Bool) (f : S → S) [Ord Action] [Inhabited Action] [Monad m] : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let l₁ ← nextLoc
    let l₂ ← nextLoc 
    pure {
        toProgramGraph := {
          transitions := RBMap.fromList [⟨l₁,[ProgramTransition.mk (.some guard) a f l₂]⟩] compare,
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
 Process a `foreverUntil`. We take the mainline linear code of the foreverUntil and turn it into a loop with
 a nonDet branch at the end. To do this we add loops from all flowOut nodes to all flowIn nodes.
-/
def intoLoop {S : Type} [Ord Action] [Inhabited Action] [Monad m]
    (p : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S))
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let p ← p
    let newTransitions : List (Nat × Nat) := List.join <| p.flowOut.map (fun ⟨_,n₁⟩ => p.flowIn.map (fun n₂ => ⟨n₁,n₂⟩))
    let pg' := newTransitions.foldl (fun g ⟨l₁,l₂⟩ => g.addTransition l₁ l₂ (fun _ => true) default id) p.toProgramGraph
    pure { p with toProgramGraph := pg' }

-- Since foreverUntil is partial it won't show up in the normal wormhole transformation. But we
-- know what the final graph should look like, so we still generate a program graph.
def ForeverUntilProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        []
        []
        [⟨"foreverUntil", fun args mk => do
            let inLoop ← mk true #[] (args.get! 2)
            `(intoLoop $(TSyntax.mk inLoop))⟩]


/-
 While building a ProgramGraph we store flowIn/flowOut edges that don't lead to an actual node, and will
 get filled in later. This is to reduce the amount of redundant nodes. However when visualizing or checking
 these flows don't show up. So this function will add nodes to server as source/sink for those flow edges.
-/
def reifyFlows {Act StateVariables : Type} [Ord Act] [Inhabited Act] [Monad m]
    (outLabel : String)
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
          locationLabels := pg.locationLabels.insert outNode [outLabel]
        },
        flowIn := [],
        flowOut := [],
        jumpTo := pg.jumpTo
    }

/-
  At the end of a program, for proper termination we add a terminal node that self-loops. This are added as a target of all the
  flowOut nodes.
-/
def addTerminalNode {Act StateVariables : Type} [Ord Act] [Inhabited Act] [Monad m]
    (terminalLabel : String)
    (pg : MetaProgramGraph Nat Act StateVariables)
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    let terminalNode ← nextLoc 
    let outTransitions := pg.flowOut.map (fun ⟨a,l⟩ => ⟨l,[ProgramTransition.mk .none a id terminalNode]⟩)
    let terminalSelfLoop := ⟨terminalNode,[ProgramTransition.mk .none default id terminalNode]⟩
    let allTransitions := mergeRBMaps pg.transitions (RBMap.fromList (terminalSelfLoop :: outTransitions) compare)
    pure {
        toProgramGraph := {
          transitions := allTransitions,
          starts := if pg.flowIn.length == 0
                    then pg.starts
                    else pg.flowIn,
          locationLabels := pg.locationLabels.insert terminalNode [terminalLabel]
        },
        flowIn := [],
        flowOut := [],
        jumpTo := pg.jumpTo
    }

/-
  Route all flow out nodes of a program into a single self-loop node, representing
  a spot to wait for other threads to progress and (eventually) finish.
-/
def addJoinNode {Act StateVariables : Type} [Ord Act] [Inhabited Act] [Monad m]
    (joinLabel : String)
    (pg : MetaProgramGraph Nat Act StateVariables)
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    let joinNode ← nextLoc 
    let outTransitions := pg.flowOut.map (fun ⟨a,l⟩ => ⟨l,[ProgramTransition.mk .none a id joinNode]⟩)
    let joinSelfLoop := ⟨joinNode,[ProgramTransition.mk .none default id joinNode]⟩
    let allTransitions := mergeRBMaps pg.transitions (RBMap.fromList (joinSelfLoop :: outTransitions) compare)
    pure {
        toProgramGraph := {
          transitions := allTransitions,
          starts := if pg.flowIn.length == 0
                    then pg.starts
                    else pg.flowIn,
          locationLabels := pg.locationLabels.insert joinNode [joinLabel]
        },
        flowIn := [],
        flowOut := [⟨default,joinNode⟩],
        jumpTo := pg.jumpTo
    }

/-
 Remove flowOut transitions with non-default actions. We need this because
 when interleaving, combining two flowOuts with non-default actions is problematic.
-/
def onlyDefaultFlowOuts {Act StateVariables : Type} [Ord Act] [BEq Act] [Inhabited Act] [Monad m]
    (pg : MetaProgramGraph Nat Act StateVariables)
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    let ⟨defaultFlowOuts, nondefaultFlowOuts⟩ := pg.flowOut.partition (fun ⟨a,n⟩ => a == default)
    -- for each non-default flowOut, we create a new node as a destination for the flowOut, and
    -- create a default flowOut from that new node
    --let pg := { pg with flowOut := defaultFlowOuts }
    nondefaultFlowOuts.foldlM
        (fun p ⟨a,n⟩ => do
            let newLoc ← nextLoc
            let newGraph := p.toProgramGraph.addTransition n newLoc (fun _ => true) a id
            let newFlowOut := p.flowOut.cons ⟨default, newLoc⟩
            pure {p with toProgramGraph := newGraph, flowOut := newFlowOut})
        pg

/-
 Interleave - combine two program graphs in parallel.
-/
def concurrentPrograms [Ord Act] [Inhabited Act] [BEq Act] [Monad m] [BEq StateVariables]
    (p₁ p₂ : ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables))
    :  ProgramGraphBuilderT m (MetaProgramGraph Nat Act StateVariables) := do
    -- build the programs and combine them. FlowOuts are problematic so we eliminate them by
    -- applying onlyDefaultFlowOuts
    let p₁ ← p₁ >>= onlyDefaultFlowOuts
    let p₂ ← p₂ >>= onlyDefaultFlowOuts
    let pX := interleaveProgramGraphs p₁.toProgramGraph p₂.toProgramGraph .none
    -- We assume a fork/join model where all the concurrent programs start at once and the combined program
    -- does not complete until all programs complete. Thus both flowIn and flowOut are cartesian products of
    -- the original values.
    let flowInX := List.join <| p₁.flowIn.map (fun n₁ => p₂.flowIn.map (fun n₂ => OProd.mk n₁ n₂))
    -- Note that flowOuts only have default actions (because we ran onlyDefaultFlowOuts above) so we ignore
    -- the actions present in both p₁.flowOut and p₂.flowOut and just build product flowOuts with default actions.
    let flowOutX : List (Act × OProd Nat Nat) :=
        List.join <| p₁.flowOut.map (fun ⟨_,n₁⟩ => p₂.flowOut.map (fun ⟨_,n₂⟩ => ⟨default, OProd.mk n₁ n₂⟩))
    -- the combined program has vertex indices (OProd Nat Nat) so we need to convert them back into
    -- just Nat
    let locations := pX.allLocations
    let remapping : RBMap (OProd Nat Nat) Nat compare ←
        locations.foldlM
            (fun m v => do
                let l ← nextLoc
                pure <| m.insert v l)
            RBMap.empty
    let remapLoc : OProd Nat Nat → Nat := fun nn => remapping.findD nn 1000
    let remapTransition : ProgramTransition (OProd Nat Nat) Act StateVariables → ProgramTransition Nat Act StateVariables :=
        fun ⟨g,a,e,n⟩ => ⟨g,a,e,remapLoc n⟩
    -- now we need to remap everything : transitions, labels, starts, flowIn, flowOut
    let pN : ProgramGraph Nat Act StateVariables := {
        transitions := pX.transitions.fold (fun m k v => m.insert (remapLoc k) (v.map remapTransition)) RBMap.empty,
        locationLabels := pX.locationLabels.fold (fun m k v => m.insert (remapLoc k) v) RBMap.empty,
        starts := pX.starts.map remapLoc
        }
    let flowInX := flowInX.map remapLoc
    let flowOutX := flowOutX.map <| fun ⟨a,nn⟩ => ⟨a, remapLoc nn⟩
    -- we throw away jumpTo, I'm not sure how that would work anyways
    pure <| {
        toProgramGraph := pN,
        flowIn := flowInX,
        flowOut := flowOutX,
        jumpTo := RBMap.empty
    }

def programGraphTransformers
    (effTransform : ProcessEffect) 
    (heffTransform : ProcessHEffect)
    (directTransforms : List (String × TransformerAppSyntax))
    (pureTransform : Expr → TermElabM Syntax)
    : List (String × TransformerAppSyntax) :=
    directTransforms ++ [
        ⟨"send", fun args mk => do
            let eff := args.get! 0
            let op := args.get! 3
            effTransform eff op
        ⟩,
        ⟨"hLift", fun args mk => do
            let heff := args.get! 0
            let op := args.get! 3
            let fork := args.get! 4
            heffTransform heff op fork mk
        ⟩,
        ⟨"hSend", fun args mk => do
            let heff := args.get! 0
            let op := args.get! 3
            let fork := args.get! 4
            heffTransform heff op fork mk
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

def programGraphPure : Expr → TermElabM Syntax :=
    fun e => `(basicStep default)


def buildProgramGraphWormhole (processors : List WormholeCallbacks) (processPure : Expr → TermElabM Syntax)
    : RBMap String TransformerAppSyntax compare :=
    let forEffects := List.join <| processors.map (fun w => w.effects)
    let forHEffects := List.join <| processors.map (fun w => w.heffects)
    let forDirect := List.join <| processors.map (fun w => w.direct)
    RBMap.fromList
        (programGraphTransformers
            (dispatchEffectProcessor forEffects)
            (dispatchHEffectProcessor forHEffects)
            forDirect processPure)
        compare


-- final monad implementing the state and IO
--genWormhole2 genFSM >: monadFuncs (processOps exampleProcessors) processPure :<


-- for unfolded program graphs we use vertex labels that have both a text string for human
-- readability, and a set of APBits for LTL/CTL checking
structure UnfoldedVertexLabel (APList : List String) : Type where
    (textLabel : String)
    (atomicProps : APBits APList)

instance : Inhabited (UnfoldedVertexLabel APList) where
    default := UnfoldedVertexLabel.mk "" APBits.empty


def toFSM {S : Type} -- State Variables
    [ToString S] [BEq S] [Ord S] [StateCardinality S]
    (p : MetaProgramGraph Nat String S)
    (initialStates : List S)
    (stateAP : S → List String)
    (APList : List String)
    : FSM Nat (APBits APList) String :=
    FSM.compactFSM <|
        FSM.onlyReachableFSM <|
            unfoldProgramGraph
                p.toProgramGraph
                (fun n s xs =>
                    let totalAP : List String := xs ++ stateAP s
                    listToAPBits totalAP
                    )
                id
                initialStates

def toFSMLabeled {S : Type} -- State Variables
    [ToString S] [BEq S] [Ord S] [StateCardinality S]
    (p : MetaProgramGraph Nat String S)
    (initialStates : List S)
    (stateAP : S → List String)
    (APList : List String)
    : FSM Nat (UnfoldedVertexLabel APList) String :=
    FSM.compactFSM <|
        FSM.onlyReachableFSM <|
            unfoldProgramGraph
                p.toProgramGraph
                (fun n s xs =>
                    let totalAP : List String := xs ++ stateAP s
                    let AP : APBits APList := listToAPBits totalAP
                    UnfoldedVertexLabel.mk (toString n ++ "|" ++ String.intercalate "/" (decodeAPBits AP)) AP
                    )
                id
                initialStates


def toVizAutomata {APList : List String} (a : FSM Nat (UnfoldedVertexLabel APList) String) : Json :=
    toJson <|
        VizGraph.toVizFSM
            (FSM.onlyReachableFSM <| a)
            (fun uf => uf.textLabel)
            id
            "/start"
            "/end"
            []

def toVizProgram (p : MetaProgramGraph Nat String SV) : Json :=
    toJson <| VizGraph.toVizProgramGraph p.toProgramGraph id

def toVizUnfoldedProgram [StateCardinality StateVariables] [BEq StateVariables] [Ord StateVariables] [ToString StateVariables]
    (p : MetaProgramGraph Nat String StateVariables)
    (stateToAP : StateVariables → List String)
    (relevantAP : List String) : Json :=
    if h : StateCardinality.sSize StateVariables > 0
    then toVizAutomata <| toFSMLabeled p [StateCardinality.genState ⟨0,h⟩] stateToAP relevantAP
    else Json.bool false

end MetaProgramGraph
