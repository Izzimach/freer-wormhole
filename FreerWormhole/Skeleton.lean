-- Use wormhole to generate a tree-like data structure representing the freer monad.
-- We check for applications of bind/pure/ and convert them into branches and leaves of the tree.
-- When we see a command (usually generated by Freer.send) that gets it own leaf.
-- Splits such as if/then/else and pattern matches are mapped to "NonDet" since we
-- can't reliably evaluate the test. Also recursion has to be handled specially since
-- it doesn't fit into the pure/bind structure.

import Lean

import FreerWormhole.Effects.Freer
--import FreerWormhole.Effects.HEff
import FreerWormhole.Effects.StdEffs

import FreerWormhole.Wormhole

open Lean Elab Command Meta Term

open Freer Effect HEffect Wormhole StdEffs



-- Skeleton representation of a (Freer effs x). When walking the Freer monad, commands
-- are converted into a type c and pure values are converted into a type t.
inductive FreerSkeleton (c t : Type) : Type where
| Error : String → FreerSkeleton c t
| Empty : FreerSkeleton c t
| Pure : t → FreerSkeleton c t
| Command : c → FreerSkeleton c t
| Bind : FreerSkeleton c t → FreerSkeleton c t → FreerSkeleton c t
| NonDet : FreerSkeleton c t → FreerSkeleton c t → FreerSkeleton c t
| Recursive : String → FreerSkeleton c t → FreerSkeleton c t
| Recurse : String → FreerSkeleton c t
    deriving Repr


def dumpFreerSkeleton [ToString c] [ToString t]: FreerSkeleton c t → String
    | .Error e => "Error : " ++ e
    | .Empty   => "Empty"
    | .Pure x => "Pure " ++ toString x
    | .Command c => "Command: " ++ toString c
    | .Bind a b => dumpFreerSkeleton a ++ " >>= " ++ dumpFreerSkeleton b
    | .NonDet a b => "(" ++ dumpFreerSkeleton a ++ " || " ++ dumpFreerSkeleton b ++ ")"
    | .Recursive s r => "{{Recursive " ++ s ++ " :: " ++ dumpFreerSkeleton r ++ "}}"
    | .Recurse s => "Call Recurse //" ++ s++ "//"



namespace FreerSkel

instance [ToString c] [ToString t] : ToString (FreerSkeleton c t) where
    toString := dumpFreerSkeleton

def listToNonDetFreer (targetType : Expr) (l : List Expr) : Expr :=
    match l with
    | List.nil => Lean.mkApp (Lean.mkConst ``FreerSkeleton.Empty) targetType
    | List.cons h List.nil => h
    | List.cons h t => Lean.mkAppN (Lean.mkConst ``FreerSkeleton.NonDet) #[targetType, h, listToNonDetFreer targetType t]

def monadFuncs
    (cmdTransform : Expr → Expr → TermElabM Syntax) 
    (pureTransform : Expr → TermElabM Syntax) : 
        RBMap String TransformerAppSyntax compare :=
    RBMap.ofList
    [
        ⟨"send", fun args mk => do
            let eff := args.get! 0
            let op := args.get! 3
            let v ← cmdTransform eff op
            `(FreerSkeleton.Command $(TSyntax.mk v))
        ⟩,
        ⟨"bind", fun args mk => do
            let a₁ := args.get! 4
            let a₂ := args.get! 5
            let r₁ ← mk true #[] a₁
            let r₂ ← mk true #[mkStrLit "bad argument"] a₂
            `(FreerSkeleton.Bind $(TSyntax.mk r₁) $(TSyntax.mk r₂))
        ⟩,
        ⟨"Pure", fun args mk => do
            let a := args.get! 2
            let v ← pureTransform a
            `(FreerSkeleton.Pure $(TSyntax.mk v))
        ⟩,
        ⟨"pure", fun args mk => do
            let a := args.get! 3
            let v ← pureTransform a
            `(FreerSkeleton.Pure $(TSyntax.mk v))
        ⟩,
        -- if
        ⟨"ite", fun args mk => do
            logInfo <| args.get! 0
            let b₁ ← mk true args (args.get! 3)
            let b₂ ← mk true args (args.get! 4)
            `(FreerSkeleton.NonDet $(TSyntax.mk b₁) $(TSyntax.mk b₂))
        ⟩,
        -- decidible if
        ⟨"dite", fun args mk => do
            let b₁ ← mk true args (args.get! 3)
            let b₂ ← mk true args (args.get! 4)
            `(FreerSkeleton.NonDet $(TSyntax.mk b₁) $(TSyntax.mk b₂))
        ⟩,
        -- A recursive call
        ⟨"Recurse", fun args mk => do
            match args.get! 0 with
            | .lit (.strVal s) => `(FreerSkeleton.Recurse $(Syntax.mkStrLit s))
            | _ => `(FreerSkeleton.Recurse "Error: bad recurse id")
        ⟩,
        -- Wrapper around a recursive function
        ⟨"fix", fun args mk => do
            let recVar ← mkFreshExprMVar (mkConst ``String)
            let recId := recVar.mvarId!.name.toString
            recVar.mvarId!.assign (mkStrLit recId)
            let recFun := args.get! 4
            let recursiveCall := mkAppN (mkConst ``FreerSkeleton.Recurse) #[recVar]
            let recurseBody ← mk true #[mkStrLit "arg", recursiveCall] recFun
            `(FreerSkeleton.Recursive $(Syntax.mkStrLit recId) $(TSyntax.mk recurseBody))
        ⟩
    ]
    

--
-- some test monads
--


def noop3 [HasEffect NoopEffect m] : Freer m Nat := do noop; pure 3

def dumpArgh [HasEffect IOEffect m] : Nat → Freer m Nat := fun n => do
    if h : n = 0
    then pure 4
    else do
        ioEff (IO.println "argh")
        dumpArgh (n-1)


def wormHoleX : Freer [NoopEffect, IOEffect] Nat := do
    let z ← noop3
    if z < 3
        then dumpArgh 3
        else pure 3


-- this makes the pretty-printer show universe levels
set_option pp.universes true
set_option pp.fullNames true


--#eval walkExpr ((do ioEff (IO.println "argh"); pure (ULift.up 4)) : Freer [IOEffect] (ULift Nat))
--#eval walkExpr (noop : Freer [NoopEffect,IOEffect] PUnit)



def ProcessEffects := List (String × TermElabM Syntax)

def processE : ProcessEffects :=
    [
        ⟨"NoopEffect", `(fun (op : Type 1) (x : op) => "Noop!")⟩,
        ⟨"IOEffect", `(fun (op : Type 1) (o : StdEffs.IOX) => "IO!")⟩
    ]

def cmdX : ProcessEffects → Expr → Expr → TermElabM Syntax := fun pr eff op => do
    match eff.getAppFn with
    | .const effName lvls => do
        let eNameEnd := effName.components.getLastD "_"
        match List.lookup eNameEnd.toString pr with
        | .some fm => do
            withFreshMacroScope <| do
                let et ← inferType op
                let etStx ← `(?et)
                let opStx ← `(?op)
                let etVar ← elabTerm etStx .none
                let opVar ← elabTerm opStx (.some et)
                etVar.mvarId!.assign et
                opVar.mvarId!.assign op
                let f ← fm
                `($(TSyntax.mk f) ?et ?op)
        | .none => `("no handler for effect " ++ $(Syntax.mkStrLit effName.toString))
    | _ => `("malformed effect")

def pureX : Expr → TermElabM Syntax :=
    fun e => `(Unit.unit)


genWormhole2 xx >: monadFuncs (cmdX processE) pureX :<

#check goWormhole2 (pure 3)
#check goWormhole2 (noop3 : Freer [NoopEffect] Nat)  --wormHoleX.{0}
#reduce goWormhole2 wormHoleX

def x : FreerSkeleton String Unit := goWormhole2 wormHoleX

#reduce x

--#eval goWormhole2 wormHoleX

end FreerSkel


namespace HEffSkel

open Effect HEffect StdEffs StdHEffs

def transact
    [HasHEffect (hLifted (StateEff Nat)) heffs]
    [HasHEffect (hLifted ThrowEff) heffs]
    [HasHEffect (CatchHEff (onlyRet Unit)) heffs]
      : Hefty heffs Nat :=
    do
    putH 1
    catchH
        (do putH 2; throwH)
        (do putH 3)
    getH

inductive HCommand (t : Type) where
| Command0 : String → HCommand t
| HCommand : String → Array (FreerSkeleton (HCommand t) t) → HCommand t 
    deriving Repr

-- For higher-order effects (Hefty) we have to handle the higher-order send and bind.
-- An hLift just has the appropriate parts forwarded to normal effect/command processing.
def heffFuncs
    (cmdTransform : Expr → Expr → TermElabM Syntax) 
    (heffTransform : Expr → Expr → Expr → ((a : Bool) → Array Expr → Expr → TermElabM (wormholeResult a)) → TermElabM Syntax)
    (pureTransform : Expr → TermElabM Syntax) : 
        RBMap String TransformerAppSyntax compare :=
    let baseFuncs := FreerSkel.monadFuncs cmdTransform pureTransform
    List.foldl (fun a (Prod.mk s f) => a.insert s f) baseFuncs
        [
        ⟨"hLift", fun args mk => do
            let eff := args.get! 0
            let op := args.get! 3
            let v ← cmdTransform eff op
            `(FreerSkeleton.Command (HCommand.Command0 $(TSyntax.mk v)))
        ⟩,
        ⟨"hSend", fun args mk => do
            logInfo args
            let heff := args.get! 1
            let cmd := args.get! 3
            let fork := args.get! 4
            let v ← heffTransform heff cmd fork mk
            `(FreerSkeleton.Command $(TSyntax.mk v))
        ⟩,
        ⟨"hBind", fun args mk => do
            let a₁ := args.get! 3
            let a₂ := args.get! 4
            let r₁ ← mk true #[] a₁
            let r₂ ← mk true #[mkStrLit "bad argument"] a₂
            `(FreerSkeleton.Bind $(TSyntax.mk r₁) $(TSyntax.mk r₂))
        ⟩
        ]

-- higher-order effect processors need the fork Expr so they can pull out appropriate branches/forks
def ProcessHEff := Expr → Expr → Expr → (rec : (a : Bool) → Array Expr → Expr → TermElabM (wormholeResult a)) →TermElabM Syntax  

def heffX : List (String × ProcessHEff) → ProcessHEff :=
    fun transformers heff cmd fork rec =>
        match heff.getAppFn with
        | .const c levels => do
            logInfo "heffect..."
            logInfo fork
            match c.components.getLast? with
            | .some i => do
                let z := Syntax.mkStrLit i.toString
                match transformers.lookup i.toString with
                | .some tr => tr heff cmd fork rec
                | .none => `(HCommand.Command0 <| "unhandled effect: " ++ $z)
            | .none =>
                let z := Syntax.mkStrLit c.toString
                `(HCommand.Command0 <| "unnamed heff" ++ $z)
        | _ => `(HCommand.Command0 <| "heffX error")

def processE : List (String × TermElabM Syntax) :=
    [
        ⟨"StateEff", `(fun (op : Type 1) x => match x with | StateOp.Put _ => "PutState" | StateOp.Get => "GetState" | StateOp.Modify _ => "ModifyState")⟩,
        ⟨"ThrowEff", `(fun (op : Type 1) x => "Throw")⟩
    ]


def stripLambda : Expr → Expr
    | .lam n arg b bi => b 
    | e@_ => e

-- given an Expr of the form (fun x => match x with |a => branch1 | b => branch2 |....) this
-- will strip off the fun and match and collate the branches into an array of Exprs #[branch1, branch2,...].
-- If the expr passed in is not of this form, returns Option.none
def unfoldFork (e : Expr) : MetaM (Option (Array Expr)) :=
    let x := stripLambda e
    if x.isApp
    then do
        let f := x.getAppFn
        let args := x.getAppArgs
        let branches := args.toList.drop 3
        let branches := branches.map stripLambda
        pure (.some branches.toArray)
    else pure .none

def processHE : List (String × ProcessHEff) :=
    [
        ⟨"CatchHEff", fun heff cmd fork rec => do
            let forks ← unfoldFork fork
            match forks with
            | .some v => do
                let evals ← v.mapM (rec true #[])
                v.toList.forM (fun x => logInfo x)
                let a₁ ← `(FreerSkeleton.Error "a")
                let evals : Array (TSyntax `term) := evals.map (TSyntax.mk)
                `(HCommand.HCommand "catchEff" [ $evals,* ].toArray)
            | .none => `(HCommand.HCommand "catchEff?" #[])⟩
    ]

genWormhole2 hskel >: heffFuncs (FreerSkel.cmdX processE) (heffX processHE) FreerSkel.pureX :<

#check goWormhole2 (pure 3 : Freer [IOEffect] Nat)

#check goWormhole2 (@transact [CatchHEff (onlyRet Unit), hLifted ThrowEff, hLifted (StateEff Nat)] _ _ _)

def xW : FreerSkeleton (HCommand Unit) Unit := 
    goWormhole2 (@transact [CatchHEff (onlyRet Unit), hLifted ThrowEff, hLifted (StateEff Nat)] _ _ _)

#eval xW

end HEffSkel