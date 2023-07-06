--
-- Use wormhole to generate an automata representation of a program from a Freer monad
--

import Lean.Meta

import SolifugidZ.Basic
import SolifugidZ.LabeledGraph
import SolifugidZ.FSM
import SolifugidZ.VizGraph
import SolifugidZ.Bisimulation
import SolifugidZ.StutterBisimulation

import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole


open Lean Elab Expr Command Meta Term

open EffM Effect HEffM HEffect
open Wormhole

open LabeledGraph FSM VizGraph

namespace WormholeAutomata

/-
Our automata contains a state machine/FSM for the general connectivity, and
some extra notation.
- Nodes are indexed by Nat
- Nodes have a list of String labels
- Edges have a single String label (which may be "")
- "Exotransitions" are transitions to nodes outside the current automata, used to represent
   exceptions and recursion.  Each key is a string ID along with a list of nodes that transition to whatever
   is represented by that ID
-/
structure AltAutomata : Type where
    -- the states and transitions
    (fsm : FSM Nat (List String) String)
    -- list of calls to named nodes of other FSM's, mentioned by name (String).
    (exoTransitions : RBMap String (List Nat) compare)

-- Looks for the given transition label in the set of exo transitions.
-- If found, it removes that transition label and from the set, then
-- returns a modified set of exo transition with that label removed and the target edges (vertex indices) that were found for that
-- label.
def pullExo (exot : RBMap String (List x) compare) (label : String) : (RBMap String (List x) compare × (List x)) :=
    match exot.find? label with
    | .some xs => ⟨exot.erase label, xs⟩
    | .none => ⟨exot, []⟩

def labeledNode (label : String) : AltAutomata :=
    {
        fsm :=
        {
            toLabeledGraph := fromExplicit <|
            compileGraph
                [⟨0,[]⟩, ⟨1,[label]⟩]
                [⟨0,1,""⟩]
        
            startStates := [0],
            endStates := [1]

        },
        exoTransitions := .empty
    }

def zeroNode : AltAutomata :=
    {
            fsm :=
            {
                toLabeledGraph := fromExplicit <|
                    compileGraph [⟨0,[]⟩] []
                startStates := [0],
                endStates := [0]
            },
            exoTransitions := .empty
    }

def exoNode (exoLabel : String) : AltAutomata :=
    { zeroNode with exoTransitions := RBMap.fromList [⟨exoLabel,[0]⟩] compare }

def recurseNode (exoLabel : String) : AltAutomata :=
    {
        fsm :=
        {
            toLabeledGraph := fromExplicit <|
                compileGraph [⟨0,[]⟩] []
            startStates := [0],
            endStates := []
        },
        exoTransitions := RBMap.fromList [⟨exoLabel,[0]⟩] compare
    }

def mapRBMap (m : RBMap k v c) (f : v → x) : RBMap k x c :=
    m.fold 
        (fun m' key val => m'.insert key (f val))
        .empty

def mergeRBMap (a b : RBMap k v c) (mergeVals : v → v → v) : RBMap k v c :=
    a.fold 
        (fun m' key val =>
            match m'.find? key with
            | .none => m'.insert key val
            | .some val2 => m'.insert key (mergeVals val val2))
        b

-- sequences automata A then B, merging exoTransitions
def sequenceAutomata : AltAutomata → AltAutomata → AltAutomata
| ⟨fsm₁, exo₁⟩, ⟨fsm₂, exo₂⟩ =>
    -- when we sequence the start nodes of fsm₂ get "overwritten" by end nodes of fsm₁, so
    -- we look at the exo nodes of fsm₂. If any are start nodes, we record so those so that we cann
    -- add those exo labels to all end states of fsm₁
    let fsm₃ := FSM.sequenceFSMs fsm₁ fsm₂
    let skippedexo := mapRBMap exo₂ (fun v => v.filter (fun n => fsm₂.startStates.contains n))
    let ⟨fsm, remapping⟩ := FSM.compactFSMWithMapping <| fsm₃
    -- exo₁ is Left, exo₂ is Right
    let exo₁ := mapRBMap exo₁ (fun l => l.filterMap (fun n => remapping (Basic.OSum.Left n)))
    let exo₂ := mapRBMap exo₂ (fun l => l.filterMap (fun n => remapping (Basic.OSum.Right n)))
    -- any skipped exos? add those labels to nodes that were the endstates of fsm₁
    let endStates1 := fsm₁.endStates.filterMap (fun n => remapping (Basic.OSum.Left n))
    let exoX := mapRBMap skippedexo <|
        fun l => if l.length == 0
                 then []
                 else endStates1
    let mergeExo := fun a b => mergeRBMap a b (fun x y => List.eraseDups <| x ++ y)
    {
        fsm := fsm,
        exoTransitions := mergeExo exo₁ (mergeExo exo₂ exoX)
    }

-- if/then branch into two automata
def branchAutomata : AltAutomata → AltAutomata → AltAutomata
| ⟨fsm₁, exo₁⟩, ⟨fsm₂, exo₂⟩ =>
    let ⟨fsm, remapping⟩ := FSM.compactFSMWithMapping <| FSM.mergeFSMs fsm₁ fsm₂
    -- exo₁ is Left, exo₂ is Right
    let exo₁ := mapRBMap exo₁ (fun l => l.filterMap (fun n => remapping (Basic.OSum.Left n)))
    let exo₂ := mapRBMap exo₂ (fun l => l.filterMap (fun n => remapping (Basic.OSum.Right n)))
    {
        fsm := fsm,
        exoTransitions := mergeRBMap exo₁ exo₂ HAppend.hAppend
    }

/-
 Handle recursion
 
 Any recursive calls are indicated by an exoTransition with a given
 ID; all these transitions are re-routed to lead to the automata start node(s) and removed from the
 exoTransitions set. You can give these recursive edges a label (or use "" for no label).
-/
def reifyRecursion (a : AltAutomata) (recurseId : String) (label : String) : AltAutomata :=
    let ⟨fsm,exo⟩ := sequenceAutomata (labeledNode "recurseHead") a
    let ⟨exo, recursors⟩ := pullExo exo recurseId
    -- we need to convert to an explicit graph to add edges. We'll convert back to a LabeledGraph at the end
    -- using 'fromExplicit'
    let explicitGraph := fsm.toExplicit
    -- nodes in vs need to have edges back to all start nodes
    let addRecursionEdges := fun g n₁ =>
        fsm.startStates.foldl (fun g n₂ => LabeledGraph.addEdge g n₁ n₂ label) g
    let explicitGraph := recursors.foldl addRecursionEdges explicitGraph
    let fsm := { fsm with toLabeledGraph := LabeledGraph.fromExplicit explicitGraph }
    ⟨fsm,exo⟩

/-
 Handle an "exception" where the exoTransitions of one Automata are fed into
 the start states of a second automata.
 We start with two automata E and X, and a label L that indicates which
 exoTransition represents an exception (the "Throw").
 In the merged automata we have:
  - Start states are drawn from E.
  - Any exoTransitions in E with the label L are routed to the start states of X.
  - Any exoTransitions in X with the label L are left unchanged, presumably to be "caught" by a higher level handler.
  - All end states from both E and X are considered end states.
-/
def reifyException (e : AltAutomata) (x : AltAutomata) (throwId : String) (exceptionLabel : String): AltAutomata :=
    let ⟨eFSM,eExo⟩ := e
    let ⟨xFSM,xExo⟩ := x
    -- merge the two graphs and map all the relevant elements (start/end states and exo transitions)
    -- to the proper Left/Right values (e automata is Left, x automata is Right)
    let mergedGraph := LabeledGraph.mergeGraphs eFSM.toLabeledGraph xFSM.toLabeledGraph
    let startStates := eFSM.startStates.map (@Basic.OSum.Left Nat Nat)
    let endStates := eFSM.endStates.map Basic.OSum.Left ++ xFSM.endStates.map Basic.OSum.Right
    let eExo := mapRBMap eExo (fun l => l.map (@Basic.OSum.Left Nat Nat))
    let xExo := mapRBMap xExo (fun l => l.map (@Basic.OSum.Right Nat Nat))
    -- pull the throw transitions out of eExo. The remaining exos are merged with those of x
    let ⟨eExo, throwVerts⟩ := pullExo eExo throwId
    let exo := mergeRBMap eExo xExo HAppend.hAppend
    -- now add throw transition edges to the graph. We convert to and explicit graph, add edges, and convert back
    let throwGraph :=
        throwVerts.foldl
            (fun g v₁ => startStates.foldl (fun g v₂ => addEdge g v₁ v₂ exceptionLabel) g)
            mergedGraph.toExplicit
    -- compact the completed graph. This will remap all the vertex indices
    -- so we apply this remapping to all the other fields as we assemble the final struct
    -- to return
    let ⟨finalGraph, remapping⟩ := compactGraphWithMapping (fromExplicit throwGraph)
    {
        fsm := {
            toLabeledGraph := finalGraph,
            startStates := startStates.filterMap remapping,
            endStates := endStates.filterMap remapping
        },
        exoTransitions := mapRBMap exo (fun l => l.filterMap remapping)
    }

/-
  Take a given automata and loop it by connecting end nodes to the start nodes.
  The exit nodes are left intact since a `foreverUntil` can exit the loop.
-/
def loopAutomata (a : AltAutomata) : AltAutomata :=
    let eGraph := a.fsm.toExplicit
    let newEdges : List (Nat × Nat) := List.join <| a.fsm.startStates.map (fun n₂ => a.fsm.endStates.map (fun n₁ => ⟨n₁,n₂⟩))
    let eGraph := newEdges.foldl (fun g ⟨n₁,n₂⟩ => LabeledGraph.addEdge g n₁ n₂ "") eGraph
    {a with fsm.toLabeledGraph := LabeledGraph.fromExplicit eGraph}

-- for a forever loop, we loop back all end nodes and remove the exit/end states
def hardLoopAutomata (a : AltAutomata) : AltAutomata :=
    let eGraph := a.fsm.toExplicit
    let newEdges : List (Nat × Nat) := List.join <| a.fsm.startStates.map (fun n₂ => a.fsm.endStates.map (fun n₁ => ⟨n₁,n₂⟩))
    let eGraph := newEdges.foldl (fun g ⟨n₁,n₂⟩ => LabeledGraph.addEdge g n₁ n₂ "") eGraph
    {
        a with
            fsm.toLabeledGraph := LabeledGraph.fromExplicit eGraph
            fsm.endStates := []
    }



def automataTransformers
    (effTransform : ProcessEffect) 
    (heffTransform : ProcessHEffect)
    (directTransforms : List (String × TransformerAppSyntax))
    (pureTransform : Expr → TermElabM Syntax)
    : List (String × TransformerAppSyntax) :=
    directTransforms ++ [
        -- if
        ⟨"ite", fun args mk => do
            logInfo <| args.get! 0
            let b₁ ← mk true args (args.get! 3)
            let b₂ ← mk true args (args.get! 4)
            `(branchAutomata $(TSyntax.mk b₁) $(TSyntax.mk b₂))
        ⟩,
        -- decidible if
        ⟨"dite", fun args mk => do
            let b₁ ← mk true args (args.get! 3)
            let b₂ ← mk true args (args.get! 4)
            `(branchAutomata $(TSyntax.mk b₁) $(TSyntax.mk b₂))
        ⟩,
        -- A recursive call
        ⟨"recurseNode", fun args mk => do
            match args.get! 0 with
            | .lit (.strVal s) => `(recurseNode $(Syntax.mkStrLit s))
            | _ => `("Error: bad recurse id")
        ⟩,
        -- Wrapper around a recursive function
        ⟨"fix", fun args mk => do
            let recVar ← mkFreshExprMVar (mkConst ``String)
            let recId := recVar.mvarId!.name.toString
            recVar.mvarId!.assign (mkStrLit recId)
            let recFun := args.get! 4
            let recursiveCall := mkAppN (mkConst ``recurseNode) #[recVar]
            let recurseBody ← mk true #[mkStrLit "arg", recursiveCall] recFun
            `(reifyRecursion $(TSyntax.mk recurseBody) $(Syntax.mkStrLit recId) "recurse")
        ⟩,
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
        ⟨"bind", fun args mk => do
            let a₁ := args.get! 4
            let a₂ := args.get! 5
            let r₁ ← mk true #[] a₁
            let r₂ ← mk true #[mkStrLit "bad argument"] a₂
            `(sequenceAutomata $(TSyntax.mk r₁) $(TSyntax.mk r₂))
        ⟩,
        ⟨"Pure", fun args mk => do
            let a := args.get! 2
            pureTransform a
        ⟩,
        ⟨"pure", fun args mk => do
            let a := args.get! 3
            pureTransform a
        ⟩
    ]

def automataPure : Expr → TermElabM Syntax :=
    fun e => `(zeroNode)--`(labeledNode "pure")

def buildAutomataWormhole (processors : List WormholeCallbacks) (processPure : Expr → TermElabM Syntax)
    : RBMap String TransformerAppSyntax compare :=
    let forEffects := List.join <| processors.map (fun w => w.effects)
    let forHEffects := List.join <| processors.map (fun w => w.heffects)
    let forDirect := List.join <| processors.map (fun w => w.direct)
    RBMap.fromList
        (automataTransformers
            (dispatchEffectProcessor forEffects)
            (dispatchHEffectProcessor forHEffects)
            forDirect processPure)
        compare

def toVizAutomata (a : AltAutomata) (aps : List String) : Json :=
    let baseFSM := FSM.onlyReachableFSM <| AltAutomata.fsm a
    let baseFSM := {
        baseFSM with
        toLabeledGraph := StutterBisimulation.stutterBisimulationDivQuotient baseFSM.toLabeledGraph (fun a b => @Bisimulation.compareLists _ aps _ a b)
    }
    toJson <|
        toVizFSM baseFSM
             (fun vl => String.intercalate "/" vl)
             id
             "/start"
             "/end"
             []

end WormholeAutomata
