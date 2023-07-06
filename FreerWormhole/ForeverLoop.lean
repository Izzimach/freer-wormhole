--
-- We have special handling for a loop that goes forever (and can't be shown to terminate)
-- A specific partial function is used to generate an infinite loop or a do..until loop,
-- and we also provide a wormhole processor to produce the proper automata/program graph constructs
-- to represent that loop.
--

import Lean

import FreerWormhole.Wormhole
import FreerWormhole.Skeleton
import FreerWormhole.Automata
import FreerWormhole.MetaProgramGraph


namespace ForeverLoop

open Lean Elab Command Meta Term

open Wormhole WormholeSkeleton WormholeAutomata MetaProgramGraph


-- An endless loop - this is partial so the elaborator will hide it behind an `opaque` Expr,
-- but we can write a transformer specifically for foreverUntil that knows how to build the correct
-- FSM or other final data structure.
partial
def foreverUntil [Monad m] (mainLine : m Bool) : m Unit := do
    if (← mainLine)
    then pure ()
    else foreverUntil mainLine

partial
def foreverLoop [Monad m] (loopcode : m Unit) : m Unit := do
    loopcode
    foreverLoop loopcode
    
-- Since foreverUntil is partial it won't show up in the normal wormhole transformation. So we
-- transform it into a loop via the recursive constructor.
def ForeverLoopSkeletonProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        []
        []
        [⟨"foreverUntil", fun args mk => do
            let inLoop ← mk true #[] (args.get! 2)
            let recVar ← mkFreshExprMVar (mkConst ``String)
            let recId := recVar.mvarId!.name.toString
            recVar.mvarId!.assign (mkStrLit recId)
            -- we wrap the loop in .Recursive and some stuff onto the end after the loop:
            --  A nonet branch that either loops back (Recurse) or drops out of the loop (pure)
            `(FreerSkeleton.Recursive $(Syntax.mkStrLit recId)
                (FreerSkeleton.Bind
                    $(TSyntax.mk inLoop) 
                    (FreerSkeleton.NonDet
                        (FreerSkeleton.Recurse $(Syntax.mkStrLit recId))
                        (FreerSkeleton.Pure PUnit.unit))))
         ⟩,
         ⟨"foreverLoop", fun args mk => do
            let inLoop ← mk true #[] (args.get! 2)
            let recVar ← mkFreshExprMVar (mkConst ``String)
            let recId := recVar.mvarId!.name.toString
            recVar.mvarId!.assign (mkStrLit recId)
            -- we wrap the loop in .Recursive and loop back.
            -- Note there's no Nondet branch here like in foreverUntil
            `(FreerSkeleton.Recursive $(Syntax.mkStrLit recId)
                (FreerSkeleton.Bind
                    $(TSyntax.mk inLoop) 
                    (FreerSkeleton.Recurse $(Syntax.mkStrLit recId))))
         ⟩]


-- Since foreverUntil is partial it won't show up in the normal wormhole transformation. But we
-- know what the final graph should look like, so we still generate a program graph.
def ForeverLoopAutomataProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        []
        []
        [⟨"foreverUntil", fun args mk => do
            let inLoop ← mk true #[] (args.get! 2)
            `(WormholeAutomata.loopAutomata $(TSyntax.mk inLoop))
            ⟩,
         ⟨"foreverLoop", fun args mk => do
            let inLoop ← mk true #[] (args.get! 2)
            `(WormholeAutomata.hardLoopAutomata $(TSyntax.mk inLoop))⟩]


-- Since foreverUntil is partial it won't show up in the normal wormhole transformation. But we
-- know what the final graph should look like, so we still generate a program graph.
def ForeverLoopProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        []
        []
        [⟨"foreverUntil", fun args mk => do
            let inLoop ← mk true #[] (args.get! 2)
            `(MetaProgramGraph.intoLoop $(TSyntax.mk inLoop))
            ⟩,
         ⟨"foreverLoop", fun args mk => do
            let inLoop ← mk true #[] (args.get! 2)
            `(MetaProgramGraph.hardLoop $(TSyntax.mk inLoop))
            ⟩
            ]

end ForeverLoop