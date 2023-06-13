import FreerWormhole.Effects.EffM

import FreerWormhole.Wormhole
import FreerWormhole.Automata
import FreerWormhole.MetaProgramGraph


namespace LabelEffect

open Effect EffM SupportsEffect

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
            | .inr ⟨op,h⟩ => next (show _ by rw [←h]; exact ()) PUnit.unit
    }

def runLabelEffect {effs : List Effect} : EffM (LabelEffect :: effs) x → EffM effs x :=
    fun m => handleEffect (@labelHandler effs x) m PUnit.unit


-- Attach a text annotation here in the code.
def label [SupportsEffect LabelEffect m] (l : String) : m PUnit :=
    @send LabelEffect m _ (LabelOp.Label l)

-- `noop` is basically an empty label.
def noop [SupportsEffect LabelEffect m] : m PUnit :=
    @send LabelEffect m _ (LabelOp.Label "")

--
-- effect processors for skeleton, automata, and program graph
--

def LabelEffectSkeletonProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"LabelEffect", effSyntaxMode `(fun (op : Type 1) (x : op) => "Label")⟩]
        []
        []

def LabelEffectAutomataProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"LabelEffect", effSyntaxMode `(fun (op : Type 1) x => labeledNode x.1)⟩]
        []
        []

def LabelEffectProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"LabelEffect", effSyntaxMode `(fun (op : Type 1) (x : LabelOp) => labelStep (x.1))⟩]
        []
        []

end LabelEffect