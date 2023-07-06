
import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole
import FreerWormhole.Automata

import FreerWormhole.Effects.LabelEffect
import FreerWormhole.Effects.IOEffect
import FreerWormhole.Effects.StateEffect
import FreerWormhole.Effects.ExceptionEffect
import FreerWormhole.ForeverLoop

--
-- some test monads
--

open Lean Elab Term

open Wormhole WormholeAutomata

open EffM Effect HEffM HEffect

open LabelEffect IOEffect StateEffect ExceptionEffect ForeverLoop

def noop3 [Monad m] [SupportsEffect LabelEffect m] : m Nat := do noop; pure 3

def dumpArgh [Monad m] [SupportsEffect IOEffect m] [SupportsEffect LabelEffect m] : Nat → m Nat := fun n => do
    labelBlock "dumploop" <| foreverUntil <| do
        let z := 1
        if z < 3
        then do liftIO (IO.println "argh"); pure false
        else do label "zero"; pure true
    label "enddump"
    pure 4

def stateManip [Monad m] [SupportsEffect (StateEffect Nat) m] : m Nat := do
    let z ← get
    put 4
    pure z

def wormHoleX : HEffM [LabelWrapHEffect, hLifted (StateEffect Nat), hLifted LabelEffect, hLifted IOEffect] Nat := do
    label "stage 1"
    let z ← noop3
    labelBlock "stage 2" <|do
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
        ForeverLoopAutomataProcessor
    ]
    -- pure processor
    automataPure
    :<

#check goWormhole2 (pure 3)
#check goWormhole2 (noop3 : EffM [LabelEffect] Nat)  --wormHoleX.{0}
--#reduce goWormhole2 wormHoleX

def x := (goWormhole2 wormHoleX)
#check x
#widget VizGraph.vizGraph toVizAutomata x ["stage 1", "stage 2", "stage 3", "dumploop"]

