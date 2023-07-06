
import Lean

import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole
import FreerWormhole.Skeleton
import FreerWormhole.Automata
import FreerWormhole.MetaProgramGraph


namespace LabelEffect

open Lean Elab Term Meta

open Effect EffM SupportsEffect HEffect HEffM

open Wormhole WormholeAutomata MetaProgramGraph

inductive LabelOp : Type u where
    | Label : String → LabelOp

-- The LabelEffect is essentially a noop that you can use to attach text annotations to
-- certain places in the code. When transformed into a tree or FSM the annotation should show up there as well.
def LabelEffect : Effect :=
    {
        op := LabelOp,
        ret := fun _ => PUnit
    }

def labelHandler {a : Type} : Handler a a LabelEffect effs PUnit :=
    {
        ret := fun a _ => .Pure a,
        handle := fun ou next _ =>
            match decompOU ou with
            | .inl ou' => .Impure ou' (fun x => next x PUnit.unit)
            | .inr ⟨op,h⟩ => next (show _ by subst h; exact ()) PUnit.unit
    }

def runLabelEffect {effs : List Effect} : EffM (LabelEffect :: effs) x → EffM effs x :=
    fun m => handleEffect (@labelHandler effs x) m PUnit.unit

-- Attach a text annotation here in the code.
def label [SupportsEffect LabelEffect m] (l : String) : m PUnit :=
    @send LabelEffect m _ (LabelOp.Label l)

-- `noop` is basically an empty label.
def noop [SupportsEffect LabelEffect m] : m PUnit :=
    @send LabelEffect m _ (LabelOp.Label "")


-- This attaches a label to a given block of code. Since this does nothing operationally we
-- don't bother creating an effect or HEffect
def labelBlock [Monad m] (l : String) (s : m a) : m a := s

--
-- effect processors for skeleton, automata, and program graph
--

def getWrapLabel (op : Expr) : TermElabM (TSyntax `term) :=
    withFreshMacroScope <| do
        let opStx ← `(?op)
        let opVar ← elabTerm opStx .none
        opVar.mvarId!.assign op
        `((fun op => match op with |LabelWrapCmd.LabelWrap l ret => l) ?op)

def getBlockLabel (op : Expr) : TermElabM (TSyntax `term) :=
    withFreshMacroScope <| do
        let opStx ← `(?op)
        let opVar ← elabTerm opStx .none
        opVar.mvarId!.assign op
        pure opStx

def LabelEffectSkeletonProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"LabelEffect", effSyntaxMode `(fun (op : Type 1) (x : LabelOp) => match x with |LabelOp.Label l => if l == "" then "Noop" else "Label:" ++ l)⟩]
        []
        [⟨"labelBlock",fun args mk => do
            let labelExpr := args.get! 3
            let labelStx ← getBlockLabel labelExpr
            let co := args.get! 4
            let r ← mk true #[] co
            `(FreerSkeleton.HEffect $labelStx [$(TSyntax.mk r)])⟩]

-- adds a given label to all nodes of an FSM
def labelAllAutomata (newLabel : String) (a : AltAutomata) : AltAutomata :=
    let eGraph := a.fsm.toLabeledGraph.mapLabels <|
        fun labels =>
            if !labels.contains newLabel
            then (newLabel :: labels)
            else labels
    {a with fsm.toLabeledGraph := eGraph }


def LabelEffectAutomataProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"LabelEffect", effSyntaxMode `(fun (op : Type 1) x => labeledNode x.1)⟩]
        []
        [⟨"labelBlock",fun args mk => do
            let labelExpr := args.get! 3
            let labelStx ← getBlockLabel labelExpr
            let co := args.get! 4
            let r ← mk true #[] co
            `(labelAllAutomata $labelStx $(TSyntax.mk r))⟩]

-- adds a given label to all nodes of a MetaProgramGraph
def labelAllProgramNodes {Action S : Type} [Monad m] [Ord Action]
    (newLabel : String)
    (p : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S))
    : ProgramGraphBuilderT m (MetaProgramGraph Nat Action S) := do
    let p ← p
    let allLocs := ProgramGraph.allLocations p.toProgramGraph
    let newLabels := allLocs.foldl
        (fun labels loc => match labels.find? loc with
                             | .none => labels.insert loc [newLabel]
                             | .some ls => if ls.contains newLabel
                                           then labels
                                           else labels.insert loc (newLabel :: ls))
        p.locationLabels
    pure { p with locationLabels := newLabels }



def LabelEffectProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"LabelEffect", effSyntaxMode `(fun (op : Type 1) (x : LabelOp) => labelStep (x.1))⟩]
        []
        [⟨"labelBlock",fun args mk => do
            let labelExpr := args.get! 3
            let labelStx ← getBlockLabel labelExpr
            let co := args.get! 4
            let r ← mk true #[] co
            `(labelAllProgramNodes $labelStx $(TSyntax.mk r))⟩]

end LabelEffect