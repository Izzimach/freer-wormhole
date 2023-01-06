-- use wormhole to generate a tree-like data structure representing the freer monad.

import Lean

import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.StdEffs
import FreerWormhole.Wormhole

open Lean Elab Command Term

open Freer Effect Wormhole




inductive FreerSkeleton (t : Type) where
| Error : String → FreerSkeleton t
| Empty
| Pure : (α : Type) → α → String → FreerSkeleton t
| Command : t → FreerSkeleton t 
| Bind : FreerSkeleton t → FreerSkeleton t → FreerSkeleton t
| NonDet : FreerSkeleton t → FreerSkeleton t → FreerSkeleton t

def dumpFreerSkeleton {t : Type} [ToString t] : FreerSkeleton t → String
    | .Error e => "Error : " ++ e
    | .Empty   => "Empty"
    | .Pure tx x s => "Pure " ++ s
    | .Command t => "Command: " ++ toString t
    | .Bind a b => dumpFreerSkeleton a ++ " >>= " ++ dumpFreerSkeleton b
    | .NonDet a b => "(" ++ dumpFreerSkeleton a ++ " || " ++ dumpFreerSkeleton b ++ ")"

instance [ToString t] : ToString (FreerSkeleton t) where
    toString := dumpFreerSkeleton

def listToNonDetFreer (targetType : Expr) (l :List Expr) : Expr :=
    match l with
    | List.nil => Lean.mkApp (Lean.mkConst ``FreerSkeleton.Empty) targetType
    | List.cons h List.nil => h
    | List.cons h t => Lean.mkAppN (Lean.mkConst ``FreerSkeleton.NonDet) #[targetType, h, listToNonDetFreer targetType t]


-- basic transformers for monad pure/bind and if/then/pattern matching
def skeletonTransformers (resultTypeName : Name) : List (String × TransformerApp) :=
[
    ⟨"bind",fun args mk => do
        let a₁ ← mk args (args.get! 4)
        let a₂ ← mk (Lean.mkStrLit "badArg" :: args) (args.get! 5)
        pure <| Lean.mkAppN (Lean.mkConst ``FreerSkeleton.Bind) #[(Lean.mkConst resultTypeName), a₁,a₂]⟩,
    ⟨"pure",fun args mk => do
        let et := args.get! 2
        let a := args.get! 3
        pure <| Lean.mkAppN (Lean.mkConst ``FreerSkeleton.Pure) #[Lean.mkConst resultTypeName, et, a, mkStrLit "?"]⟩,
    ⟨"ite",fun args mk => do
        let b₁ ← mk args (args.get! 3)
        let b₂ ← mk args (args.get! 4)
        pure <| Lean.mkAppN (Lean.mkConst ``FreerSkeleton.NonDet) #[Lean.mkConst resultTypeName, b₁, b₂]⟩,
    ⟨"match",fun branches mk => pure <| listToNonDetFreer (Lean.mkConst resultTypeName) branches⟩
]

--
-- quick example using wormhole to convert a do block into a Monad skeleton
--

section MonadSkel

-- transformers to process IO.println in the following example
def skeletonIOTransformers (resultTypeName : Name) : List (String × TransformerApp) :=
[
    ⟨"MonadLiftT.monadLift", fun args mk => do
        pure <| Lean.mkAppN (Lean.mkConst ``FreerSkeleton.Command) #[Lean.mkConst resultTypeName, mkStrLit "Lift"]⟩,
    ⟨"IO.FS.Stream.putStr", fun args mk => do
        pure <| Lean.mkAppN (Lean.mkConst ``FreerSkeleton.Command) #[Lean.mkConst resultTypeName, mkStrLit "putStr"]⟩
]

genWormhole genSkeleton >: (skeletonTransformers ``String ++ skeletonIOTransformers ``String) :<


#reduce goWormhole ((do IO.println "argh"; pure 3) : IO Nat)

end MonadSkel

--
-- quick example using wormhole to convert a do block of a freer monad into a skeleton
--

section FreerSkel

-- a monad that runs in the elaborator and generates transformers for the elements of the ExampleMonad
def tx : TermElabM (List (Expr × Expr)) := do
    let tm : List (Prod (TermElabM Syntax) (TermElabM Syntax)) :=
        [⟨`(IO),
              `(fun (a : Type) (z : IO a) => "IO")⟩,
         ⟨`(Id),
              `(fun (a : Type) (z : Id a) => "Id")⟩
        ]
    let runProd : TermElabM Syntax × TermElabM Syntax → TermElabM (Expr × Expr) :=
        fun ⟨n,t⟩ => do
           let nE ← elabTerm (← n) Option.none
           let tE ← elabTerm (← t) Option.none
           pure <| ⟨nE,tE⟩
    List.mapM runProd tm

-- final monad implementing the state and IO
genWormholeSend freerSkel $: Lean.mkConst ``String >: skeletonTransformers ``String :< tx :$    

def getNat [HasEffect NoopEffect m] : Freer m (ULift Nat) := do noop; pure (ULift.up 3)

def dumpArgh.{u} [HasEffect IOEffect.{u} m] : Freer.{u+1} m (ULift Nat) := do
    ioEff0 (IO.println "argh")
    pure (ULift.up 4)

def wormHoleX.{u} : Freer.{u+1} [NoopEffect.{u+1}, IOEffect.{u}] (ULift Nat) := do
    let z ← getNat
    if z.down < 3
        then dumpArgh
        else pure (ULift.up 3)

#eval walkExpr ((do ioEff0 (IO.println "argh"); pure (ULift.up 4)) : Freer [IOEffect] (ULift Nat))
#reduce goWormhole wormHoleX

end FreerSkel
