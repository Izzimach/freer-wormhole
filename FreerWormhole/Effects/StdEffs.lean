
import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.Heff


namespace StdEffs

open Freer Effect HEffect

--
-- Standard State Effect, with get and put
--

inductive StateOp (s : Type) : Type 1 where
    | Put : s → StateOp s
    | Get : StateOp s
    | Modify : (s → s) → StateOp s 


def StateEff (s : Type) : Effect :=
    {
        op := StateOp s,
        ret := fun op => match op with
                         | .Put _ => Unit
                         | .Get   => s
                         | .Modify _ => s
    }

def stateHandler {s : Type} : Handler a (a × s) (StateEff s) effs s :=
    {
        ret := fun a s => Freer.Pure ⟨a,s⟩,
        handle := fun ou next s =>
            match ou with
            | .Leaf l => match l with
                         | .Put x => next () x
                         | .Get   => next s s
                         | .Modify f => let s' := f s; next s' s'
            | .Node ou' => .Impure ou' (fun x => next x s)
    }

def runState {s x : Type} (init : s) : Freer (StateEff s :: effs) x → Freer effs (x × s) :=
    fun m => handleFreer (@stateHandler x effs s ) m init

def get {s : Type} {effs : List Effect} [HasEffect (StateEff s) effs] : Freer effs s :=
    @send (StateEff s) effs _ StateOp.Get

def put {s : Type} {effs : List Effect} [HasEffect (StateEff s) effs] (x : s) : Freer effs Unit :=
    @send (StateEff s) effs _ (StateOp.Put x)

def modify  {s : Type} {effs : List Effect} [HasEffect (StateEff s) effs] (f : s → s) : Freer effs s :=
    @send (StateEff s) effs _ (StateOp.Modify f)


def getH { s : Type} {heffs : List HEffect} [HasHEffect (hLifted (StateEff s)) heffs] : Hefty heffs s :=
    @hLift (StateEff s) _ _ StateOp.Get

def putH {s : Type} {heffs : List HEffect} [HasHEffect (hLifted (StateEff s)) heffs] (x : s) : Hefty heffs Unit :=
    @hLift (StateEff s) _ _ (StateOp.Put x)

def modifyH {s : Type} {effs : List Effect} [HasHEffect (hLifted (StateEff s)) heffs] (f : s → s) : Hefty heffs s :=
    @hLift (StateEff s) _ _ (StateOp.Modify f)


--
-- Identity effect, used for no-op or placeholder. This is different from the
-- NilEffect which is used to terminate effects chains and is more like a "not effect"
--

inductive Noop : Type u where
    | Noop

def NoopEffect : Effect :=
    {
        op := Noop,
        ret := fun _ => PUnit
    }

def noopEffHandler {a : Type} : Handler a a NoopEffect effs PUnit :=
    {
        ret := fun a _ => Freer.Pure a,
        handle := fun ou next _ =>
            match ou with
            | .Leaf l => next PUnit.unit PUnit.unit
            | .Node ou' => .Impure ou' (fun x => next x PUnit.unit)
    }

def runNoopEff {effs : List Effect} : Freer (NoopEffect :: effs) x → Freer effs x :=
    fun m => handleFreer (@noopEffHandler effs x) m PUnit.unit


def noop {effs : List Effect} [HasEffect NoopEffect effs] : Freer effs PUnit :=
    @send NoopEffect effs _ Noop.Noop

def noopH {heffs : List HEffect} [HasHEffect (hLifted NoopEffect) heffs] : Hefty heffs PUnit :=
    @hLift NoopEffect heffs _ Noop.Noop

--
-- A generic IO effect to run an (mostly?) arbitrary IO effect
--


inductive IOX : Type 1 where
    | IOOp : (a : Type) → IO a → IOX

def IOEffect : Effect :=
    {
        op := IOX,
        ret := fun z => match z with
                        | IOX.IOOp a m => a
    }

def runIOEff {a : Type} : Freer [IOEffect] a → IO a
    | .Pure a => pure a
    | .Impure (.Leaf l) next =>
        match l with
        | .IOOp _ m =>    m >>= (fun x => runIOEff (next x))

-- special case of runIOEff for Unit, because of odd lifting
def runIOEffUnit : Freer [IOEffect] PUnit → IO Unit
    | .Pure _ => pure ()
    | .Impure (.Leaf l) next =>
        match l with
        | .IOOp _ m =>    m >>= (fun x => runIOEffUnit (next x))

def ioEff {a : Type} {effs : List Effect} [HasEffect IOEffect effs] (m : IO a) : Freer effs a :=
    @send IOEffect effs _ (IOX.IOOp a m)


def ioEffH {a : Type} {heffs : List HEffect} [HasHEffect (hLifted IOEffect) heffs] (m : IO a) : Hefty heffs a :=
    @hLift IOEffect heffs _ (IOX.IOOp a m)


unsafe
def stateHandlerRef {s a : Type} (sRef : IO.Ref s) [HasEffect IOEffect effs] : Handler a a (StateEff s) effs Unit :=
    {
        ret := fun a _ => Freer.Pure a,
        handle := fun ou next _ =>
            match ou with
            | .Leaf l => match l with
                         | .Put x => do ioEff (sRef.set x); next () ()
                         | .Get   => do let v ← ioEff sRef.get; next v () 
                         | .Modify f => do
                              let v ← ioEff sRef.take
                              ioEff <| sRef.set (f v)
                              next v ()
            | .Node ou' => .Impure ou' (fun x => next x ())
    }

-- Alternate version of runState that uses a IO.Ref variable, suitable for shared state accessed by multiple
-- threads.
-- The underlying runtime uses C++ atomics for Put/Get/Modify so your changes are atomic, but the code will spinlock
-- while waiting for a Ref to be available. If you need to wait for a while or do condition checking you might
-- want to use a Mutex or Condvar instead.
unsafe
def runStateRef {s x : Type} (init : s) [HasEffect IOEffect effs] : Freer (StateEff s :: effs) x → Freer effs x :=
    fun m => do
        let r ← ioEff <| IO.mkRef init  
        handleFreer (@stateHandlerRef effs s _ r _) m ()



-- A State Effect that also allows for efficient waiting using a mutex. You can do this with C++ atomics by
-- spinlocking but if you're waiting a lot it's usually better to yield the thread and wake up when
-- your data is "ready".
inductive SignalStateOp (S : Type) : Type 1 where
    | Get : SignalStateOp S
    | Put : S → SignalStateOp S
    | Modify : (a : Type) → (S → a × S) → SignalStateOp S
    -- Waits for the state to satisfy the given condition and then modifies it atomically
    | Wait : (S → Bool) → (S → S) → SignalStateOp S

def SignalStateEff (s : Type) : Effect :=
    {
        op := SignalStateOp s,
        ret := fun op => match op with
                         | .Get   => s
                         | .Put _ => Unit
                         | .Modify a _ => a
                         | .Wait _ _ => s
    }

def ssGet {s : Type} {effs : List Effect} [HasEffect (SignalStateEff s) effs] : Freer effs s :=
    @send (SignalStateEff s) effs _ SignalStateOp.Get

def ssPut {s : Type} {effs : List Effect} [HasEffect (SignalStateEff s) effs] (x : s) : Freer effs Unit :=
    @send (SignalStateEff s) effs _ (SignalStateOp.Put x)

def ssModify  {s a : Type} {effs : List Effect} [HasEffect (SignalStateEff s) effs] (f : s → a × s) : Freer effs a :=
    @send (SignalStateEff s) effs _ (SignalStateOp.Modify a f)

def ssWait  {s : Type} {effs : List Effect} [HasEffect (SignalStateEff s) effs] (test : s → Bool) (f : s → s) : Freer effs s :=
    @send (SignalStateEff s) effs _ (SignalStateOp.Wait test f)


def ssGetH {s : Type} {heffs : List HEffect} [HasHEffect (hLifted (SignalStateEff s)) heffs] : Hefty heffs s :=
    @hLift (SignalStateEff s) heffs _ SignalStateOp.Get

def ssPutH {s : Type} {heffs : List HEffect} [HasHEffect (hLifted (SignalStateEff s)) heffs] (x : s) : Hefty heffs Unit :=
    @hLift (SignalStateEff s) heffs _ (SignalStateOp.Put x)

def ssModifyH  {s a : Type} {heffs : List HEffect} [HasHEffect (hLifted (SignalStateEff s)) heffs] (f : s → a × s) : Hefty heffs a :=
    @hLift (SignalStateEff s) heffs _ (SignalStateOp.Modify a f)

def ssWaitH  {s : Type} {heffs : List HEffect} [HasHEffect (hLifted (SignalStateEff s)) heffs] (test : s → Bool) (f : s → s) : Hefty heffs s :=
    @hLift (SignalStateEff s) heffs _ (SignalStateOp.Wait test f)


def signalStateHandler {s : Type} (mtx : IO.Mutex s) (cv : IO.Condvar) [HasEffect IOEffect effs] : Handler a a (SignalStateEff s) effs Unit :=
    {
        ret := fun a () => Freer.Pure a,
        handle := fun ou next () =>
            match ou with
            | .Leaf l => match l with
                         | .Get   => do
                             let s ← ioEff <| mtx.atomically MonadState.get
                             next s ()
                         | .Put x => do
                             ioEff <| mtx.atomically <| MonadState.set x
                             ioEff <| cv.notifyAll
                             next () ()
                         | .Modify _ f => do
                             let x ← ioEff <| mtx.atomically (MonadState.modifyGet (fun s => f s))   
                             ioEff <| cv.notifyAll
                             next x ()
                         | .Wait pr f =>  do
                             let s ← ioEff <|
                                 mtx.atomicallyOnce
                                 cv
                                 (MonadState.modifyGet (fun s => ⟨pr s, s⟩))
                                 (do let s' ← MonadState.modifyGet (fun s => ⟨f s, f s⟩); cv.notifyAll; pure s')
                             next s ()
            | .Node ou' => .Impure ou' (fun x => next x ())
    }

def runSignalState {s x : Type} (init : s) [HasEffect IOEffect effs] : Freer (SignalStateEff s :: effs) x → Freer effs (x × s) :=
    fun m => do
        let mtx ← ioEff <| IO.Mutex.new init
        let cv ← ioEff <| IO.Condvar.new
        let a ← handleFreer (@signalStateHandler effs x s mtx cv _) m ()
        let s' ← ioEff <| mtx.atomically MonadState.get
        pure ⟨a,s'⟩

def runSignalState' {s x : Type} (init : s) [HasEffect IOEffect effs] : Freer (SignalStateEff s :: effs) x → Freer effs x :=
    fun m => do
        let ⟨a,s'⟩ ← runSignalState init m
        pure a

def runSignalStateMutex {s x : Type} (mtx : IO.Mutex s) (cv : IO.Condvar) [HasEffect IOEffect effs] : Freer (SignalStateEff s :: effs) x → Freer effs x :=
    fun m => handleFreer (@signalStateHandler effs x s mtx cv _) m ()

end StdEffs


namespace StdHEffs

open Freer Effect HEffect

inductive ThrowOp : Type u where
    | Throw : String → ThrowOp

def ThrowEff : Effect :=
    {
        op := ThrowOp,
        ret := fun _ => ULift <| Fin 0
    }

def throwHandler : Handler a (Option a) ThrowEff effs Unit := 
    {
        ret := fun a () => Freer.Pure (Option.some a),
        handle := fun ou next () => match ou with
                                    | .Leaf z => match z with | .Throw err => Freer.Pure Option.none
                                    | .Node ou' => Freer.Impure ou' (fun x => next x ())
    }

def runThrow : Freer (ThrowEff :: effs) x → Freer effs (Option x) := fun m => handleFreer throwHandler m ()

def throwH {heffs : List HEffect} [HasHEffect (hLifted ThrowEff) heffs] : Hefty heffs PUnit :=
    hBind (@hLift ThrowEff _ _ (ThrowOp.Throw "argh"))
          (fun _ => hPure ())


-- "Universe-of-Types" basically mapping from values in one type to types in that same universe
structure UoT : Type 1 where
    (choice : Type)
    (uotResult : choice → Type)

-- Used with catch; (CatchHEff (onlyRet a)) is a try/catch that always return a, on success OR failure
def onlyRet (a : Type) : UoT :=
    {
        choice := PUnit,
        uotResult := fun _ => a
    }



inductive CatchOp (catchDispatch : UoT) : Type 1 where
    | Catch : catchDispatch.choice → CatchOp catchDispatch

inductive ExceptResult : Type 1 where
    | Success : ExceptResult
    | Failure : ExceptResult

def CatchFork (a : Type) : Effect :=
    {
        -- possible values to pass to the fork, to choose which fork
        op := ExceptResult,
        -- return type from various forks, these can be different or the same
        ret := fun z => match z with
                        | .Success => a   -- success returns catch result
                        | .Failure => a
    }

def CatchHEff (dispatch : UoT) : HEffect :=
    {
        cmd := CatchOp dispatch,
        fork := fun op => CatchFork (dispatch.uotResult op.1),
        retH := fun e => dispatch.uotResult e.1
    }

def catchH {result : Type} {heffs : List HEffect} [HasHEffect (CatchHEff (onlyRet result)) heffs] 
      (run : Hefty heffs result)
      (onError : Hefty heffs result) : Hefty heffs result :=
    @hSend heffs (CatchHEff (onlyRet result)) _ (CatchOp.Catch PUnit.unit)
        (fun pz => match pz with
                   | ExceptResult.Success => run
                   | .Failure => onError)



def elabCatch : Elab1 (CatchHEff (onlyRet Unit)) heffs (ThrowEff :: effs) :=
    fun elab0 =>
    fun op phi next =>
        match op with
        | .Leaf c =>
            match c with
            | .Catch PUnit.unit =>
                let r₁ := runThrow (phi .Success)
                let r₂ := fun (z : Option _) => match z with
                                    | Option.none => bindFreer (phi .Failure) next
                                    | Option.some x => next x
                (weaken r₁) >>= r₂
        | .Node hou' => elab0 hou' phi next



inductive AtomicStateOp (StateVariables : Type) : Type 1 where
    | AtomicIf : (StateVariables → (Bool × StateVariables)) → Type → AtomicStateOp StateVariables
    | Fork : Nat → AtomicStateOp StateVariables


inductive AtomicStateBranch : Type 1 where
    | ThenBranch : AtomicStateBranch
    | ElseBranch : AtomicStateBranch

def AtomicStateBranchEff (a : Type) : Effect :=
    {
        -- possible values to pass to the fork, to choose which fork
        op := AtomicStateBranch,
        -- both branches need to return the same type
        ret := fun _ => a
    }

def AtomicStateForkEff (n : Nat) : Effect  :=
    {
        op := ULift (Fin n),
        ret := fun _ => PUnit
    }

-- AtomicStateHEff models a set of processes that indirectly communicate by modifying
-- a single set of shared state variables. The state variables are protected by a mutex so
-- all modifications/queries are atomic.
def AtomicStateHEff (StateVariables : Type) : HEffect :=
    {
        cmd := AtomicStateOp StateVariables,
        fork := fun g => match g with
                         | .AtomicIf m t => AtomicStateBranchEff t
                         | .Fork n => AtomicStateForkEff n
        retH := fun g => match g with
                         | .AtomicIf m t => t
                         | .Fork n => PUnit
    }


def atomicIf {result : Type} {heffs : List HEffect} [HasHEffect (AtomicStateHEff StateVariables) heffs] 
    (test : StateVariables → (Bool × StateVariables))
    (thenBranch : Hefty heffs result)
    (elseBranch : Hefty heffs result)
    : Hefty heffs result :=
    @hSend heffs (AtomicStateHEff StateVariables) _ (AtomicStateOp.AtomicIf test result)
        (fun pz => match pz with
                   | .ThenBranch => thenBranch
                   | .ElseBranch => elseBranch)


def atomicFork {heffs : List HEffect} [HasHEffect (AtomicStateHEff StateVariables) heffs]
    (processes : List (Hefty heffs PUnit))
    : Hefty heffs PUnit :=
    @hSend heffs (AtomicStateHEff StateVariables) _ (AtomicStateOp.Fork processes.length)
        (fun (x : ULift (Fin processes.length)) => processes[x.down])


def runForks {n : Nat} {effs : List Effect} [HasEffect StdEffs.IOEffect effs]
    (pr : (ULift (Fin n)) → Freer effs PUnit) (runner : Freer effs PUnit → IO Unit) (ix : Fin n) : Freer effs PUnit := do
        let _ ← StdEffs.ioEff <| IO.asTask (runner <| pr (ULift.up ix)) Task.Priority.dedicated
        if h : ix.val ≠ 0
        then runForks pr runner (Fin.mk (Nat.pred ix.val) (by apply (@Nat.lt_of_lt_of_le _ ix.val n); apply Nat.pred_lt h; apply Nat.le_of_lt; exact ix.isLt))
        else pure ()
    termination_by runForks _ _ ix => ix.val

def elabAtomicState {effs : List Effect} [HasEffect StdEffs.IOEffect effs]
    (runner : Freer (StdEffs.SignalStateEff StateVariables :: effs) PUnit → IO Unit)
    : Elab1 (AtomicStateHEff StateVariables) heffs (StdEffs.SignalStateEff StateVariables :: effs) :=
    fun elab0 =>
    fun op phi next =>
        match op with
        | .Leaf c =>
            match c with
            | .AtomicIf t result => do
                let b ← StdEffs.ssModify t
                let branch := if b
                              then (phi .ThenBranch)
                              else (phi .ElseBranch)
                branch >>= next
            | .Fork n => do
                if h : n ≠ 0
                then runForks phi runner (@Fin.mk n (Nat.pred n) (Nat.pred_lt h))
                else pure ()
                next ()
        | .Node hou' => elab0 hou' phi next

end StdHEffs



section testEffs

open Freer Effect HEffect StdEffs StdHEffs


def transact
    [HasHEffect (hLifted (StateEff Nat)) heffs]
    [HasHEffect (hLifted ThrowEff) heffs]
    [HasHEffect (CatchHEff (onlyRet Unit)) heffs]
      : Hefty heffs Nat :=
    do
    putH 1
    catchH
        (do putH 2; throwH)
        (do putH 3; pure ())
    getH

def elabTransact : Elaboration [ CatchHEff (onlyRet Unit), hLifted ThrowEff, hLifted (StateEff Nat)]
                               [ ThrowEff, StateEff Nat] :=
    elabCatch
    <| elabEff ThrowEff
    <| elabLast (StateEff Nat)

def runTransact : Freer [ThrowEff, StateEff Nat] a → (Option a × Nat) :=
    fun m => runEff <| runState 3 <| runThrow m

#eval runTransact <| elaborate elabTransact <| transact

def printArghs [HasHEffect (hLifted IOEffect) heffs] [HasHEffect (hLifted NoopEffect) heffs] : Hefty heffs PUnit := do
    ioEffH (IO.println "argh")
    ioEffH (IO.println "argh")
    noopH
    ioEffH (IO.println "argh")

-- Higher order effects need an elaboration phase followed by a run phase.
-- Here we defined the elaboration phase.
def elabDump : Elaboration [hLifted NoopEffect, hLifted IOEffect] [NoopEffect, IOEffect] :=
     elabEff NoopEffect
     <| elabLast IOEffect


#eval runIOEffUnit <| runNoopEff <| elaborate elabDump <| printArghs


end testEffs