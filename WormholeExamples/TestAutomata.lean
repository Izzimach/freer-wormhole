
import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole
import FreerWormhole.Automata

import FreerWormhole.Effects.LabelEffect
import FreerWormhole.Effects.IOEffect
import FreerWormhole.Effects.StateEffect
import FreerWormhole.Effects.ExceptionEffect

--
-- some test monads
--

open Lean Elab Term

open Wormhole WormholeAutomata

open EffM Effect HEffM HEffect

open LabelEffect IOEffect StateEffect ExceptionEffect

def noop3 [Monad m] [SupportsEffect LabelEffect m] : m Nat := do noop; pure 3

def dumpArgh [Monad m] [SupportsEffect IOEffect m] [SupportsEffect LabelEffect m] : Nat → m Nat := fun n => do
    foreverUntil <| do
        label "dumpLoop"
        let z := 1
        if z < 3
        then do liftIO (IO.println "argh"); label "io1"; pure false
        else do label "zero"; pure true
    label "enddump"
    pure 4

def stateManip [Monad m] [SupportsEffect (StateEffect Nat) m] : m Nat := do
    let z ← get
    put 4
    pure z

def wormHoleX : EffM [StateEffect Nat, LabelEffect, IOEffect] Nat := do
    label "stage 1"
    let z ← noop3
    label "stage 2"
    let _ ←
        if z < 3
        then dumpArgh 3
        else stateManip
    label "stage 3"
    pure 5

genWormhole2 automata >: buildAutomataWormhole
    -- effect processors
    [
        LabelEffectAutomataProcessor,
        IOEffectAutomataProcessor,
        StateEffectAutomataProcessor,
        ExceptionEffectAutomataProcessor,
        ForeverUntilAutomataProcessor
    ]
    -- pure processor
    automataPure
    :<

#check goWormhole2 (pure 3)
#check goWormhole2 (noop3 : EffM [LabelEffect] Nat)  --wormHoleX.{0}
--#reduce goWormhole2 wormHoleX

--#check goWormhole2 wormHoleX
#widget VizGraph.vizGraph toVizAutomata (goWormhole2 wormHoleX)
#widget VizGraph.vizGraph toVizAutomata (goWormhole2 (dumpArgh 3 : EffM [LabelEffect, IOEffect] Nat))

