-- Deconstruct freer monads generated by FreerMacro


import Lean
import Lean.Parser

open Lean Elab Expr Command Meta Term MVarId

namespace Wormhole

def spaceN (n : Nat) : String := String.mk <| List.replicate n ' '

partial
def goExpr (t : Expr) (indent : Nat) : MetaM Unit := do
  let preSpace := spaceN indent
  let dumpX := fun s => IO.println <| preSpace ++ s
  match (← instantiateMVars t) with
  | bvar ix => dumpX <| "bvar=" ++ toString ix
  | fvar fid => dumpX <| "fvar=" ++ toString fid.name
  | mvar mid => dumpX <| "mvar=" ++ toString mid.name
  | sort lvl => dumpX <| "sort"
  | const n levels => dumpX <| "const=" ++ n.toString
  | app f arg => dumpX "app "; goExpr f (indent+1); goExpr arg (indent+1)
  | lam n arg body _ => dumpX ("lam > " ++ n.toString); goExpr arg (indent+1); goExpr body (indent+1)
  | forallE n a b _ => dumpX ("forall " ++ n.toString); goExpr a (indent+1); goExpr b (indent+1)
--  | letE n t v b => dumpX ("let " ++ n.toString); goExpr t (indent+1); goExpr v (indent+1); goExpr (b.instantiate1 v) (indent+1)
  | letE n t v b _ => do
      dumpX ("let " ++ n.toString)
      goExpr t (indent+1)
      goExpr v (indent+1)
      goExpr b (indent+1)
  | lit (Literal.natVal n) => dumpX <| "lit=" ++ toString n
  | lit (Literal.strVal s) => dumpX <| "lit=" ++ s
  | mdata md e => dumpX "mdata"
  | proj n ix e => dumpX "proj"


def walkExpr (thing : Syntax) : TermElabM Expr := do
  let thingExpr ← elabTerm thing Option.none
  let e ← getEnv
  /-let zi := e.find? (Name.mkSimple "zzz")
  match zi with
  | Option.some (.defnInfo v) => do
      IO.println "zzz type: "
      goExpr v.type 0
  | _ => pure ()-/
  let et ← inferType thingExpr
  IO.println "thing type: "
  goExpr et 0
  IO.println "thing expression: "
  goExpr thingExpr 0
  --logInfo <| thingExpr
  pure <| Lean.mkConst `Nat.zero


-- The forall value in a type is basically an argument: forall x (forall y z) is "x → y → z"
-- This takes the set of nested foralls and breaks them into a list of argument types
def unfoldForalls : Expr → List Expr
| forallE n a rest _ => a :: unfoldForalls rest
| x => [x]

-- given some name from a ConstantInfo returns true if this is a match call (match_1, match_2, etc.)
def isMatchCall : Name → Bool := fun n =>
    match n.components.getLast? with
    | Option.none => false
    | Option.some v => String.isPrefixOf "match_" v.toString


elab "walkExpr" thing:term : term => walkExpr thing

-- A TransformerApp takes a list of arguments (as Exprs) and a recursive function to
-- call on child Expr's (this will usually be runWormhole partially applied to a transformer list) and constructs an
-- Expr from that.
def TransformerApp : Type := Array Expr → (Array Expr → Expr → TermElabM Expr) → TermElabM Expr

-- Dirty beta-reduce. We try to beta reduce functions, with the expectation that some
-- expressions will be malformed since we may not have all the information we need.
def magicBR (argStack : Array Expr) (funcBody : Expr) (offset : Nat) : Expr :=
    match funcBody with
    | bvar ix => @Option.getD Expr (argStack.get? (offset - ix)) (Lean.mkStrLit "Bad bound variable")
    | app f arg => Expr.app (magicBR argStack f offset) (magicBR argStack arg offset)
    | lam n e c z => Expr.lam n e (magicBR argStack c (offset + 1)) z
    | x => x


--
-- transform a Lean Expr tree using a lookup-list of TransformerApp elements
--
partial def runWormhole (transformers : List (String × TransformerApp)) (argStack : Array Expr) (e : Expr) : TermElabM Expr := do
    match (← instantiateMVars e) with
    | const c _ => do
        let fullName := c.toString
        --match c.components.getLast? with
        --| Option.none => pure <| Lean.mkStrLit fullName
        --| Option.some l => 
            --match transformers.lookup l.toString with
            match transformers.lookup fullName with
            | Option.some f => f argStack (runWormhole transformers)
            | Option.none => do
                let e ← getEnv
                let v := e.find? c
                match v with
                | Option.none => pure <| Lean.mkStrLit ("Unknown value named " ++ toString c)
                | Option.some ci => do
                    match ci.value? with
                    | Option.none => do
                        logInfo argStack
                        pure <| Lean.mkStrLit ("no value for constantinfo of " ++ toString c ++ " constantinfo=" ++ toString ci.name ++ " ctor?=" ++ toString ci.isCtor ++ " inductive?=" ++ toString ci.isInductive)
                    | Option.some val =>
                        match (isMatchCall c), (transformers.lookup "match") with
                        | true, Option.some matchBuild => do
                            let et ← inferType val
                            let matchArgs := unfoldForalls et
                            -- In a match "function", the first two args are motive and actual value, so we skip them.
                            -- The last argument of the type is the result, so ignore that too.
                            logInfo matchArgs
                            let branchCount := matchArgs.length - 3
                            -- pull the branches out of the argument stack
                            let branches := List.toArray <| List.take branchCount <| List.drop 2 argStack.toList
                            let breakBranches ← Array.sequenceMap branches (fun z => runWormhole transformers argStack z)
                            matchBuild (breakBranches) (runWormhole transformers)
                        | _, _ => runWormhole transformers argStack val
    | app f arg => runWormhole transformers (List.toArray <| arg :: (argStack.toList)) f
    | lam _ _ body _ => do
        -- try to substitute in bound variables and then skeletonize it
        let peBody := magicBR argStack body 0
        runWormhole transformers argStack peBody
    | bvar ix => pure <| Option.getD (argStack.get? ix) (Lean.mkStrLit "Error: bad bound variable")
    | letE n t v body _ => do
        --logInfo <| "letE, stack: " ++ argStack
        let peBody := magicBR argStack body 0
        runWormhole transformers argStack peBody
    | proj ty idx struct => do
        let structVal ← runWormhole transformers argStack struct
        let e ← getEnv
        let debugStr :="proj:" ++ toString ty ++ "," ++ toString idx ++ "/" ++ toString structVal
        match getStructureInfo? e ty with
        | Option.none => pure <| mkStrLit debugStr
        | Option.some info => do
            match StructureInfo.getProjFn? info idx with
            | Option.none => pure <| mkStrLit debugStr
            | Option.some projName => do
                match transformers.lookup projName.toString with
                -- I though we would need to append structVal to here, but it was already dumped
                -- onto the stack
                | Option.some f => f argStack (runWormhole transformers)
                | Option.none => do
                    logInfo debugStr
                    logInfo argStack
                    pure <| mkStrLit (debugStr ++ "/noMatch:" ++ toString projName)
                --magicSkeleton transformers (structVal :: argStack) (mkConst projName)
    | fvar _ => do
        logInfo <| "don't know what to do with fvar:" ++ toString e
        pure <| Lean.mkStrLit "fvar"
    | mvar _ => do
        logInfo <| "don't know what to do with mvar:" ++ toString e
        pure <| Lean.mkStrLit "mvar"
    | sort _ => do
        logInfo <| "don't know what to do with sort:" ++ toString e
        pure <| Lean.mkStrLit "sort"
    | mdata _ _ => do
        logInfo <| "don't know what to do with mdata:" ++ toString e
        pure <| Lean.mkStrLit "mdata"
    | _ => do
        logInfo <| "zort! I don't know what to do with expression term:" ++ ctorName e ++ toString e
        pure <| Lean.mkStrLit <| "zort" ++ ctorName e ++ "/" ++ toString e


-- wormhole re-written to find function applications
partial def wormhole2 (transformers : Std.RBMap String TransformerApp compare) (argStack : Array Expr) (e : Expr) : TermElabM Expr := do
    let e ← instantiateMVars e
    match e with
    | .app _ _ => do
        let fn := e.getAppFn
        let args := e.getAppArgs
        wormhole2 transformers (Array.append args argStack) fn
    | .const c _ => do
        logInfo <| "const: " ++ (String.intercalate "/" <| c.components.map toString)
        logInfo argStack
        match c.components.getLast? with
        | .none => pure <| mkStrLit "app, no function name!"
        | .some n => do
            --logInfo (← e.getAppArgs.mapM instantiateMVars)
            --pure <| mkStrLit ("app,  function name = " ++ n.toString)
            let tr := transformers.find? n.toString
            match tr with
            | .some tf => do
                logInfo <| "applying transformer for " ++ n.toString
                let tresult ← tf argStack (wormhole2 transformers)
                logInfo <| "transform result for " ++ n.toString ++ " :"
                logInfo tresult
                pure tresult
            | .none => do
                let env ← getEnv
                let v := env.find? c
                match v with
                | Option.none => pure <| Lean.mkStrLit ("Cannot find constant named " ++ toString c)
                | Option.some cr => do
                    match cr.value? with
                    | Option.none => pure <| mkStrLit ("No value for const - " ++ c.toString)
                    | Option.some s => wormhole2 transformers argStack s
    | .lam bn bt body bi => do
        logInfo <| "lambda, arg name=" ++ bn.toString ++ ", args=" ++ argStack.toList.toString
        if argStack.size = 0
        then do
            logInfo "no args for lambda"
            wormhole2 transformers #[] body
        else do
            let result := e.beta argStack
            logInfo "beta reduce result:"
            logInfo result
            --pure <| mkStrLit "lambda"
            wormhole2 transformers #[] result
    | proj ty idx struct => do
        -- for a projection we need to lookup the struct and then find the relevant field
        let structVal ← wormhole2 transformers argStack struct
        let e ← getEnv
        let debugStr :="proj:" ++ toString ty ++ "," ++ toString idx ++ "/" ++ toString structVal
        match getStructureInfo? e ty with
        | Option.none => pure <| mkStrLit debugStr
        | Option.some info => do
            match StructureInfo.getProjFn? info idx with
            | Option.none => pure <| mkStrLit debugStr
            | Option.some projName => do
                -- at this point we have the relevant field name/constructor, so we apply
                -- the usual lookup/transform step as for const
                match transformers.find? projName.toString with
                -- I though we would need to append structVal to here, but it was already dumped
                -- onto the stack
                | Option.some tf => tf argStack (wormhole2 transformers)
                | Option.none => do
                    logInfo debugStr
                    logInfo argStack
                    pure <| mkStrLit (debugStr ++ "/noMatch:" ++ toString projName)
    | fvar _ => do
        logInfo <| "don't know what to do with fvar:" ++ toString e
        pure <| Lean.mkStrLit "fvar"
    | mvar _ => do
        logInfo <| "don't know what to do with mvar:" ++ toString e
        pure <| Lean.mkStrLit "mvar"
    | sort _ => do
        logInfo <| "don't know what to do with sort:" ++ toString e
        pure <| Lean.mkStrLit "sort"
    | mdata _ _ => do
        logInfo <| "don't know what to do with mdata:" ++ toString e
        pure <| Lean.mkStrLit "mdata"
    | _ => do
        logInfo <| "zort! I don't know what to do with expression term:" ++ ctorName e ++ toString e
        pure <| Lean.mkStrLit <| "zort" ++ ctorName e ++ "/" ++ toString e

syntax (name := throughWormhole) "goWormhole" term : term
syntax (name := wormholed) "goWormhole2" term : term


-- standard macro to generate a wormhole, transforming Lean expressions according to a list of transforms
-- you provide.
set_option hygiene false in
elab "genWormhole" wormholeName:ident " >: " transforms:term " :< " : command => do
    let skelCommand ← 
        `(@[termElab Wormhole.throughWormhole]
          def $wormholeName : TermElab := fun stx _ => do
              let e ← elabTerm (Syntax.getArg stx 1) Option.none
              runWormhole $transforms #[] e
         )
    elabCommand skelCommand

set_option hygiene false in
elab "genWormhole2" wormholeName:ident " >: " transforms:term " :< " : command => do
    let skelCommand ← 
        `(@[termElab Wormhole.wormholed]
          def $wormholeName : TermElab := fun stx _ => do
              let e ← elabTerm (Syntax.getArg stx 1) Option.none
              wormhole2 $transforms #[] e
         )
    elabCommand skelCommand


genWormhole2 ww >: Std.RBMap.empty :<

#check goWormhole2 ((3 : Nat) + 3)

end Wormhole
