-- use wormhole to generate a tree-like data structure representing the freer monad.

import Lean

import FreerWormhole.Effects.Freer
import FreerWormhole.Effects.StdEffs
import FreerWormhole.Wormhole
import FreerWormhole.FreerTransformers

open Lean Elab Command Meta Term

open Freer Effect Wormhole FreerTransformers



inductive FreerSkeleton (t : Type u) where
| Error : String → FreerSkeleton t
| Empty
| Pure : t → FreerSkeleton t
| Command : t → FreerSkeleton t 
| Bind : FreerSkeleton t → FreerSkeleton t → FreerSkeleton t
| NonDet : FreerSkeleton t → FreerSkeleton t → FreerSkeleton t

def dumpFreerSkeleton {t : Type} [ToString t] : FreerSkeleton t → String
    | .Error e => "Error : " ++ e
    | .Empty   => "Empty"
    | .Pure t => "Pure " ++ toString t
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
def skeletonTransformers (resultTypeName : Expr) : FreerTransformers :=
    {
        bind := fun args mk => do
            let a₁ ← mk args (args.get! 4)
            let a₂ ← mk (Lean.mkStrLit "badArg" :: args) (args.get! 5)
            mkAppM ``FreerSkeleton.Bind #[a₁,a₂],
        pure := fun args mk => do
            let et := args.get! 2
            let a := args.get! 3
            IO.println "pure value:"
            goExpr a 0
            mkAppM ``FreerSkeleton.Pure #[mkStrLit "?"],
        ifthenelse := fun args mk => do
            let b₁ ← mk args (args.get! 3)
            let b₂ ← mk args (args.get! 4)
            mkAppM ``FreerSkeleton.NonDet #[resultTypeName, b₁, b₂],
        patMatch := fun branches mk => pure <| listToNonDetFreer (resultTypeName) branches,
        effectMatch := fun args mk => do
            let ou := args.get! 3
            let next := args.get! 4
            --goExpr ou 0
            --logInfo next
            if ou.isAppOf (String.toName "HasEffect.inject")
            then do
                IO.println "effect:"
                let eff := ou.getArgD 3 (mkStrLit "?")
                let effLevels := eff.getAppFn.constLevels!
                IO.println effLevels
                let effName := eff.getAppFn.dbgToString
                goExpr eff 0
                mkAppM ``FreerSkeleton.Command #[mkStrLit effName]
            else mkAppM ``FreerSkeleton.Error #[mkStrLit "not an effect"]
    }

--
-- quick example using wormhole to convert a do block into a Monad skeleton
--

section MonadSkel

-- here we start with the normal monad transformers -- ignoring effectMatch since we're not using the
-- Freer monad here -- and add transformers for specific IO functions for IO.println
def skeletonIOTransformers : List (String × TransformerApp) :=
    (buildWormholeTransformers (skeletonTransformers (mkConst ``String)))
    ++
    [⟨"MonadLiftT.monadLift", fun args mk => do
        mkAppM ``FreerSkeleton.Command #[mkStrLit "Lift"]⟩,
    ⟨"IO.FS.Stream.putStr", fun args mk => do
        mkAppM ``FreerSkeleton.Command #[mkStrLit "putStr"]⟩
    ]

genWormhole genSkeleton >: skeletonIOTransformers :<


#eval mkAppN (mkConst ``FreerSkeleton.Pure) #[mkConst ``Nat, mkNatLit 3, mkStrLit "?"]
#reduce walkExpr ((do IO.println "argh"; pure 3) : IO Nat)
#reduce goWormhole ((do IO.println "argh"; pure 3) : IO Nat)
#eval goWormhole ((do IO.println "argh"; pure 3) : IO Nat)

end MonadSkel

--
-- quick example using wormhole to convert a do block of a freer monad into a skeleton
--

section FreerSkel

-- final monad implementing the state and IO
genWormhole freerSkel >: (buildWormholeTransformers <| skeletonTransformers (mkConst ``String)) :<

def getNat.{u} [HasEffect NoopEffect.{u+1} m] : Freer.{u+1} m (ULift Nat) := do noop; pure (ULift.up 3)

def dumpArgh.{u} [HasEffect IOEffect.{u} m] : Freer.{u+1} m (ULift Nat) := do
    ioEff0 (IO.println "argh")
    pure (ULift.up 4)

def wormHoleX.{u} : Freer.{u+1} [NoopEffect.{u+1}, IOEffect.{u}] (ULift Nat) := do
    let z ← getNat
    if z.down < 3
        then dumpArgh
        else pure (ULift.up 3)

#eval walkExpr ((do ioEff0 (IO.println "argh"); pure (ULift.up 4)) : Freer [IOEffect] (ULift Nat))
#eval walkExpr FreerSkeleton.Pure "?"
set_option maxRecDepth 1024

#eval goWormhole (getNat : Freer [NoopEffect] (ULift Nat))

def x : FreerSkeleton String := FreerSkeleton.Pure "?"

end FreerSkel
