import Lean

import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole
import FreerWormhole.MetaProgramGraph

import FreerWormhole.Effects.LabelEffect
import FreerWormhole.Effects.IOEffect
import FreerWormhole.Effects.StateEffect
import FreerWormhole.Effects.ExceptionEffect

--
-- some test monads
--

open Lean Elab Term

open Wormhole MetaProgramGraph

open EffM Effect HEffM HEffect

open LabelEffect IOEffect StateEffect ExceptionEffect

def noop3 [Monad m] [SupportsEffect LabelEffect m] : m Nat := do noop; pure 3

-- an "infinite loop" built on foreverUntil, which has a special wormhole transformer.
def someLoop [Monad m] [SupportsEffect IOEffect m]: m Unit :=
    foreverUntil <| do
        liftIO <| IO.println "argh"
        pure True

def stateManip [Monad m] [SupportsEffect (StateEffect Nat) m] : m Unit := do
    let _ ← modifyGet (fun s => s + 1)
    pure ()

def wormHoleX : EffM [StateEffect Nat, LabelEffect, IOEffect] Nat := do
    label "stage 1"
    someLoop
    let z ← noop3
    if z < 3 then put 8 else put 4
    label "stage 2"
    stateIf (λ s => s < 6)
            someLoop
            stateManip
    label "stage 3"
    pure 5


genWormhole2 pGraph >: buildProgramGraphWormhole
    -- effect processors
    [
        IOEffectProgramGraphProcessor,
        LabelEffectProgramGraphProcessor,
        StateEffectProgramGraphProcessor,
        ExceptionEffectProgramGraphProcessor,
        ForeverUntilProgramGraphProcessor
    ]
    -- pure processor
    programGraphPure
    :<

--#check goWormhole2 (pure 3)
--#check goWormhole2 (noop3 : EffM [LabelEffect] Nat)  --wormHoleX.{0}
#check goWormhole2 wormHoleX
#check goWormhole2 (someLoop : EffM [IOEffect] Unit)

def wh : ProgramGraphBuilderT Id (MetaProgramGraph Nat String Nat):= goWormhole2 wormHoleX

def prog : MetaProgramGraph Nat String Nat := Id.run <| ProgramGraphBuilderT.build <| goWormhole2 wormHoleX

instance : ProgramGraph.StateCardinality Nat where
    sSize := 1000
    genState := fun f => f.val

#widget VizGraph.vizGraph (toVizProgram prog)
#widget VizGraph.vizGraph (toVizUnfoldedProgram prog)
