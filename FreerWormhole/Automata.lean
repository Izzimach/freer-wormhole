--
-- Use wormhole to generate an automata representation of a program from a Freer monad
--

import Lean.Meta

import SolifugidZ.Basic
import SolifugidZ.LabeledGraph
import SolifugidZ.FSM
import SolifugidZ.VizGraph

import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.StdEffs
import FreerWormhole.Wormhole


open Lean Elab Expr Command Meta Term

open Freer Effect StdEffs Wormhole

open LabeledGraph FSM VizGraph

namespace ProgramAutomata

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
    { labeledNode "recurse" with exoTransitions := RBMap.fromList [⟨exoLabel,[0]⟩] compare }

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
    let ⟨fsm, remapping⟩ := FSM.compactFSMWithMapping <| FSM.sequenceFSMs fsm₁ fsm₂
    -- exo₁ is Left, exo₂ is Right
    let exo₁ := mapRBMap exo₁ (fun l => l.filterMap (fun n => remapping (Basic.OSum.Left n)))
    let exo₂ := mapRBMap exo₂ (fun l => l.filterMap (fun n => remapping (Basic.OSum.Right n)))
    {
        fsm := fsm,
        exoTransitions := mergeRBMap exo₁ exo₂ HAppend.hAppend
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
    let ⟨fsm,exo⟩ := sequenceAutomata (labeledNode "rec") a
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



inductive VertexLabelCommand : Type u where
    | Label : String → VertexLabelCommand

-- an effect that labels a node of the generated automata
def AutomataLabel : Effect :=
    {
        op := VertexLabelCommand,
        ret := fun _ => Unit
    }

def label [HasEffect AutomataLabel effs] (l : String) : Freer effs PUnit :=
    @send AutomataLabel effs _ (VertexLabelCommand.Label l)


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
            `(sequenceAutomata $(TSyntax.mk r₁) $(TSyntax.mk r₂))
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
        ⟩
    ]

def ProcessEffects := List (String × TermElabM Syntax)

def processE : ProcessEffects :=
    [
        ⟨"NoopEffect", `(fun (op : Type 1) (x : op) => zeroNode)⟩,
        ⟨"IOEffect", `(fun (op : Type 1) (o : StdEffs.IOX) => labeledNode "IO!")⟩,
        ⟨"AutomataLabel", `(fun (op : Type 1) (x : VertexLabelCommand) => labeledNode x.1)⟩
    ]

def cmdAutomata : ProcessEffects →  Expr → Expr → TermElabM Syntax := fun pr eff op => do
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
                `($(TSyntax.mk f) ?et ?op)
        | .none => `("no handler for effect " ++ $(Syntax.mkStrLit effName.toString))
    | _ => `("malformed effect")

def pureX : Expr → TermElabM Syntax :=
    fun e => `(zeroNode)


-- final monad implementing the state and IO
genWormhole2 genFSM >: monadFuncs (cmdAutomata processE) pureX :<

def dumpArgh [HasEffect IOEffect m] : Freer m Nat := do
    ioEff (IO.println "argh")
    pure 4

def if3 [HasEffect NoopEffect m] [HasEffect AutomataLabel m] [HasEffect IOEffect m] : Nat →  Freer m Nat :=
    fun z => do
        noop
        if z = 0
        then dumpArgh
        else if3 (z-1)

def wormHoleX : Freer [AutomataLabel, NoopEffect, IOEffect] Nat := do
    label "start"
    let y ← if3 3
    label "mid"
    noop
    label "end"
    pure y

def toVizAutomata := fun a =>
    toJson <|
        toVizFSM (FSM.onlyReachableFSM <| AltAutomata.fsm a)
             (fun vl => String.intercalate "/" vl)
             id
             "/start"
             "/end"

#check goWormhole2 wormHoleX
#widget VizGraph.vizGraph toVizAutomata (goWormhole2 wormHoleX)

#eval (reifyRecursion (recurseNode "argh") "argh" "recurse").1.toLabeledGraph.edgesFor 0



end ProgramAutomata
