
import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.HEffM

import FreerWormhole.Wormhole
import FreerWormhole.Skeleton

import FreerWormhole.Effects.LabelEffect
import FreerWormhole.Effects.IOEffect
import FreerWormhole.Effects.StateEffect
import FreerWormhole.Effects.ExceptionEffect

--
-- some test monads
--

open Lean Elab Term

open Wormhole WormholeSkeleton

open EffM Effect HEffM HEffect

open LabelEffect IOEffect StateEffect ExceptionEffect

def noop3 [Monad m] [SupportsEffect LabelEffect m] : m Nat := do noop; pure 3

def dumpArgh [Monad m] [SupportsEffect IOEffect m] : m Nat := do
    foreverUntil <| do
        liftIO (IO.println "argh")
        pure true
    pure 4


def wormHoleX : EffM [LabelEffect, IOEffect] Nat := do
    let z ← noop3
    if z < 3
        then dumpArgh
        else pure 3


genWormhole2 skel >: buildSkeletonWormhole
    [
        LabelEffectSkeletonProcessor,
        IOEffectSkeletonProcessor,
        StateEffectSkeletonProcessor,
        ExceptionEffectSkeletonProcessor,
        ForeverUntilSkeletonProcessor
    ]
    -- pure processor
    pureUnit
    :<

#check goWormhole2 (pure 3)
#check goWormhole2 (noop3 : EffM [LabelEffect] Nat)  --wormHoleX.{0}
#reduce goWormhole2 wormHoleX

def x : FreerSkeleton String Unit := goWormhole2 wormHoleX

#reduce x

--#eval goWormhole2 wormHoleX



def transact
    {heffs : List HEffect}
    [SupportsEffect (StateEffect Nat) (HEffM heffs)]
    [SupportsEffect (ThrowEffect String) (HEffM heffs)]
    [SupportsHEffect (ExceptionHEffect (onlyRet Unit)) (HEffM heffs)]
      : HEffM heffs Nat :=
    do
    put 1
    catchH
        (do put 2; throwEff "argh")
        (do put 3)
    get

def transact2
    {m : Type → Type 2}
    [Monad m]
    [SupportsEffect (StateEffect Nat) m]
    [SupportsEffect (ThrowEffect String) m]
    [SupportsHEffect (ExceptionHEffect (onlyRet Unit)) m]
      : m Nat :=
    do
    put 1
    catchH
        (do put 2; throwEff "argh")
        (do put 3)
    get



#check goWormhole2 (pure 3 : EffM [IOEffect] Nat)

def m2 : Type 2 := HEffM [ExceptionHEffect (onlyRet Unit), hLifted (ThrowEffect String), hLifted (StateEffect Nat)] Nat

#check goWormhole2 (transact2 : m2)

def xW : FreerSkeleton String Unit := goWormhole2 (transact2 : m2)

#eval xW



