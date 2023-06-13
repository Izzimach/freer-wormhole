import Lean

import FreerWormhole.Effects.EffM

-- we include IOEffect since it's used by the mutable state version of StateEffect
import FreerWormhole.Effects.IOEffect

import FreerWormhole.Wormhole
import FreerWormhole.Automata
import FreerWormhole.MetaProgramGraph

open Lean Elab Command Term Meta

open Effect EffM SupportsEffect IOEffect

open Wormhole WormholeAutomata MetaProgramGraph

namespace StateEffect

inductive StateOp (s : Type) : Type 1 where
    | Put : s → StateOp s
    | Get : StateOp s
    | ModifyGet : (s → s) → StateOp s 


--
-- Standard State Effect, with get and put and modify(get)
--
def StateEffect (s : Type) : Effect :=
    {
        op := StateOp s,
        ret := fun op => match op with
                         | .Put _ => Unit
                         | .Get   => s
                         | .ModifyGet _ => s
    }

def stateHandler {s : Type} : Handler a (a × s) (StateEffect s) effs s :=
    {
        ret := fun a s => .Pure ⟨a,s⟩,
        handle := fun ou next s =>
            match decompOU ou with
            | .inl ou' => EffM.Impure ou' (fun x => next x s)
            | .inr ⟨op,h⟩ => match op with
                            | .Put x => next (show _ by rw [←h]; exact ()) x
                            | .Get   => next (show _ by rw [←h]; exact s) s
                            | .ModifyGet f => let s' := f s; next (show _ by rw [←h]; exact s') s'
    }

def runState {s x : Type} (init : s) : EffM (StateEffect s :: effs) x → EffM effs (x × s) :=
    fun m => handleEffect (@stateHandler x effs s ) m init

def get {s : Type} [SupportsEffect (StateEffect s) m] : m s :=
    @send (StateEffect s) m _ StateOp.Get

def put {s : Type} [SupportsEffect (StateEffect s) m] (x : s) : m Unit :=
    @send (StateEffect s) m _ (StateOp.Put x)

def modifyGet {s : Type} [SupportsEffect (StateEffect s) m] (f : s → s) : m s :=
    @send (StateEffect s) m _ (StateOp.ModifyGet f)



def stateIf {s : Type} [Monad m] [SupportsEffect (StateEffect s) m] (f : s → Bool) (bThen : m a) (bElse : m a) : m a := do
    let v ← get
    if (f v)
    then bThen
    else bElse

-- IO.Ref version of stateHandler, used by `runStateRef` below
unsafe
def stateHandlerRef {s a : Type} (sRef : IO.Ref s) [HasEffect IOEffect effs] : Handler a a (StateEffect s) effs Unit :=
    {
        ret := fun a _ => EffM.Pure a,
        handle := fun ou next _ =>
            match decompOU ou with
            | .inl ou' => .Impure ou' (fun x => next x ())
            | .inr ⟨op,h⟩ => match op with
                         | .Put x => do liftIO (sRef.set x); next (show _ by rw [←h]; exact ()) ()
                         | .Get   => do let v ← liftIO sRef.get; next (show _ by rw [←h]; exact v) () 
                         | .ModifyGet f => do
                              let v ← liftIO sRef.take
                              liftIO <| sRef.set (f v)
                              next (show _ by rw [←h]; exact v) ()
    }


-- Alternate version of runState that uses a IO.Ref variable, suitable for shared state accessed by multiple
-- threads.
-- The underlying runtime uses C++ atomics for Put/Get/Modify so your changes are atomic, but the code will spinlock
-- while waiting for a Ref to be available.  So this version is best when you don't expect a lot of contention or
-- waiting for critical section access. If you need to wait for a while or perform condition checking you might
-- want to use a Mutex or Condvar instead. (used by SignaledStateEffect)
unsafe
def runStateRef {s x : Type} (init : s) [HasEffect IOEffect effs] : EffM (StateEffect s :: effs) x → EffM effs x :=
    fun m => do
        let r ← liftIO <| IO.mkRef init  
        handleEffect (@stateHandlerRef effs s _ r _) m ()

--
-- wormhole processors for the standard wormhole targets
--


def StateEffectSkeletonProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"StateEffect", effSyntaxMode `(fun (op : Type 1) x => match x with | .Put _ => "PutState" | .Get => "GetState" | .ModifyGet _ => "ModifyState")⟩]
        []
        []


def stateOpToAutomata : StateOp s → AltAutomata
| StateOp.Put _ => labeledNode "PutState"
| StateOp.Get   => labeledNode "GetState"
| StateOp.ModifyGet _ => labeledNode "ModifyState"

def StateEffectAutomataProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"StateEffect", effSyntaxMode `(fun (op : Type 1) x => stateOpToAutomata x)⟩]
        []
        []


/- If the state monad represents the actual state used in the program graph, we can
   use this Processor. -/
def StateProcessor [Monad m] : StateOp S → ProgramGraphBuilderT m (MetaProgramGraph Nat String S)
| StateOp.Put s => stateModStep "[[put]]" (fun _ => s)
| StateOp.Get => labelStep "[[get]]"
| StateOp.ModifyGet f => stateModStep "[[modify]]" f

def stateIfProcessor : TransformerAppSyntax := fun args mk => do
    --logInfo <| args
    let tst := args.get! 5
    let br₁ ← mk true #[] (args.get! 6)
    let br₂ ← mk true #[] (args.get! 7)
    withFreshMacroScope <| do
        let tstType ← inferType tst
        let tstStx ← `(?tst)
        let tstVar ← elabTerm tstStx (.some tstType)
        tstVar.mvarId!.assign tst
        `(branchProgramGraph ?tst "then" id $(TSyntax.mk br₁) (fun s => not (?tst s)) "else" id $(TSyntax.mk br₂))

partial
def foreverUntilState [Monad m] [SupportsEffect (StateEffect S) m] (test : S → Bool) (mainLine : m Unit) : m Unit := do
    mainLine
    let b : S ← get
    if (test b)
    then pure ()
    else foreverUntilState test mainLine

def foreverUntilStateProcessor : TransformerAppSyntax := fun args mk => do
    let tst := args.get! 4
    let ml ← mk true #[] (args.get! 5)
    withFreshMacroScope <| do
        let tstType ← inferType tst
        let tstStx ← `(?tst)
        let tstVar ← elabTerm tstStx (.some tstType)
        tstVar.mvarId!.assign tst
        `(loopUntilState ?tst $(TSyntax.mk ml))


def StateEffectProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"StateEffect", effSyntaxMode `(fun (op : Type 1) (c : StateOp _) => StateProcessor c)⟩]
        []
        [⟨"stateIf", stateIfProcessor⟩, ⟨"foreverUntilState", foreverUntilStateProcessor⟩]

end StateEffect
