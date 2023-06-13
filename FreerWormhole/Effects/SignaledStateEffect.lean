import FreerWormhole.Effects.EffM
import FreerWormhole.Effects.IOEffect

import FreerWormhole.Wormhole
import FreerWormhole.MetaProgramGraph


namespace SignaledStateEffect

open Effect EffM
open IOEffect SupportsEffect
open Wormhole MetaProgramGraph

inductive SignaledStateOp (S : Type) : Type 1 where
    | Get : SignaledStateOp S
    | Put : S → SignaledStateOp S
    | ModifyGet : (a : Type) → (S → a × S) → SignaledStateOp S
    -- Waits for the state to satisfy the given condition and then modifies it atomically
    | WaitModify : (S → Bool) → (S → S) → SignaledStateOp S

-- A State Effect that also allows for efficient waiting using a mutex. You can do this with C++ atomics by
-- CAS and spinlocking. However if you need to wait a long time then it's better to yield the thread and wake up later when
-- your data is ready.
def SignaledStateEffect (s : Type) : Effect :=
    {
        op := SignaledStateOp s,
        ret := fun op => match op with
                         | .Get   => s
                         | .Put _ => Unit
                         | .ModifyGet a _ => a
                         | .WaitModify _ _ => s
    }

def get {s : Type} [SupportsEffect (SignaledStateEffect s) m] : m s :=
    @send (SignaledStateEffect s) m _ SignaledStateOp.Get

def put {s : Type} [SupportsEffect (SignaledStateEffect s) m] (x : s) : m Unit :=
    @send (SignaledStateEffect s) m _ (SignaledStateOp.Put x)

def modifyGet {s a : Type} [SupportsEffect (SignaledStateEffect s) m] (f : s → a × s) : m a :=
    @send (SignaledStateEffect s) m _ (SignaledStateOp.ModifyGet a f)

def modifyState {s : Type} [SupportsEffect (SignaledStateEffect s) m] (f : s → s) : m Unit :=
    @send (SignaledStateEffect s) m _ (SignaledStateOp.ModifyGet Unit (fun s => ⟨(),f s⟩))

def waitThenModify {s : Type} [SupportsEffect (SignaledStateEffect s) m] (test : s → Bool) (f : s → s) : m s :=
    @send (SignaledStateEffect s) m _ (SignaledStateOp.WaitModify test f)

def waitFor {s : Type} [Monad m] [SupportsEffect (SignaledStateEffect s) m] (test : s → Bool) : m s := do
    @send (SignaledStateEffect s) m _ (SignaledStateOp.WaitModify test id)
    

def signaledStateHandler {s : Type} (mtx : IO.Mutex s) (cv : IO.Condvar) [HasEffect IOEffect effs] : Handler a a (SignaledStateEffect s) effs Unit :=
    {
        ret := fun a () => .Pure a,
        handle := fun ou next () =>
            match decompOU ou with
            | .inl ou' => .Impure ou' (fun x => next x ())
            | .inr ⟨op,h⟩ =>
                match op with
                | .Get   => do
                    let s ← liftIO <| mtx.atomically MonadState.get
                    next (show _ by rw [←h]; exact s) ()
                | .Put x => do
                    liftIO <| mtx.atomically <| MonadState.set x
                    liftIO cv.notifyAll
                    next (show _ by rw [←h]; exact ()) ()
                | .ModifyGet _ f => do
                    let x ← liftIO <| mtx.atomically <| MonadState.modifyGet f
                    liftIO <| cv.notifyAll
                    next (show _ by rw [←h]; exact x) ()
                | .WaitModify pr f =>  do
                    let s ← liftIO <|
                        mtx.atomicallyOnce
                            cv
                            (MonadState.modifyGet (fun s => ⟨pr s, s⟩))
                            (do let s' ← MonadState.modifyGet (fun s => ⟨f s, f s⟩); cv.notifyAll; pure s')
                    next (show _ by rw [←h]; exact s) ()
    }

-- Runs SignaledStateEffect with the provided initial state put into a Mutex. At the end returns the result as wel
-- as the final state stored in the Mutex.
def runSignaledState {s x : Type} (init : s) [HasEffect IOEffect effs] : EffM (SignaledStateEffect s :: effs) x → EffM effs (x × s) :=
    fun m => do
        let mtx ← liftIO <| IO.Mutex.new init
        let cv ← liftIO <| IO.Condvar.new
        let a ← handleEffect (@signaledStateHandler effs x s mtx cv _) m ()
        let s' ← liftIO <| mtx.atomically MonadState.get
        pure ⟨a,s'⟩

-- Works as `runSignaledState` but throws away the Mutex state and just returns the result value.
def runSignaledState' {s x : Type} (init : s) [HasEffect IOEffect effs] : EffM (SignaledStateEffect s :: effs) x → EffM effs x :=
    fun m => do
        let ⟨a,s'⟩ ← runSignaledState init m
        pure a

-- A version of `runSignaledState` that uses a Mutex and Condvar you supply instead of generating one locally.
-- Useful when you want to share the Mutex and condvar between multiple threads.
def runSignaledStateMutex {s x : Type} (mtx : IO.Mutex s) (cv : IO.Condvar) [HasEffect IOEffect effs] : EffM (SignaledStateEffect s :: effs) x → EffM effs x :=
    fun m => handleEffect (@signaledStateHandler effs x s mtx cv _) m ()

def SignaledStateProcessor [Monad m] : SignaledStateOp S → ProgramGraphBuilderT m (MetaProgramGraph Nat String S)
| .Get => labelStep "[[get]]"
| .Put s => stateModStep "[[put]]" (fun _ => s)
| .ModifyGet _ f => stateModStep "[[modifyGet]]" (fun x => (f x).2)
| .WaitModify g f => singleStep "[[waitModify]]" g f

def SignaledStateEffectProgramGraphProcessor : WormholeCallbacks :=
    WormholeCallbacks.mk
        [⟨"SignaledStateEffect", effSyntaxMode `(fun (op : Type 1) (c : SignaledStateOp _) => SignaledStateProcessor c)⟩]
        []
        []

end SignaledStateEffect
