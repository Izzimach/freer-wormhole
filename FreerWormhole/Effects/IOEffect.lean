import FreerWormhole.Effects.EffM

import FreerWormhole.Wormhole
import FreerWormhole.Automata
import FreerWormhole.MetaProgramGraph

namespace IOEffect

open Effect EffM SupportsEffect

open Wormhole WormholeAutomata MetaProgramGraph

inductive IOX : Type 1 where
    | IOOp : (a : Type) → IO a → IOX

-- Performs a certain effect in IO and returns the result. Useful for embedding IO into your
-- algebraic effect monad. Some other effects will get transformed into one or more IO operations.
def IOEffect : Effect :=
    {
        op := IOX,
        ret := fun z => match z with
                        | IOX.IOOp a m => a
    }

def runIO {a : Type} : EffM [IOEffect] a → IO a
    | .Pure a => pure a
    | .Impure ou next =>
        match decompOU ou with
        | .inr ⟨.IOOp _ o,h⟩ => o >>= (fun x => runIO (next (show _ by rw [←h]; exact x)))

-- special case of runIOEff for Unit, because of odd lifting
def runIOUnit : EffM [IOEffect] PUnit → IO Unit
    | .Pure _ => pure ()
    | .Impure ou next =>
        match decompOU ou with
        | .inr ⟨.IOOp _ o,h⟩ => o >>= (fun x => runIO (next (show _ by rw [←h]; exact x)))

def liftIO {a : Type} [SupportsEffect IOEffect m] (c : IO a) : m a :=
    @send IOEffect m _ (IOX.IOOp a c)

def IOEffectSkeletonProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"IOEffect",   effSyntaxMode `(fun (op : Type 1) (o : IOX) => "IO!")⟩]
        []
        []

def IOEffectAutomataProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"IOEffect", effSyntaxMode `(fun (op : Type 1) (o : IOX) => labeledNode "IO")⟩]
        []
        []

def IOEffectProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"IOEffect", effSyntaxMode `(fun (op : Type 1) (o : IOX) => basicStep "IO")⟩]
        []
        []

end IOEffect
