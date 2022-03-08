import Lean.Meta
import Lean.Elab
import Std
import LeanLoris.Core
open Lean Meta Elab Term Std

open Nat

namespace ProdSeq
def splitPProd? (expr: Expr) : TermElabM (Option (Expr × Expr)) :=
  do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort u)
    let β  ← mkFreshExprMVar (mkSort v)
    let a ← mkFreshExprMVar α 
    let b ← mkFreshExprMVar β 
    let f := mkAppN (Lean.mkConst ``PProd.mk [u, v]) #[α, β, a, b]
    if ← isDefEq f expr
      then
        Term.synthesizeSyntheticMVarsNoPostponing
        return some (← whnf a, ← whnf b)
      else 
        return none

def splitProd?(expr: Expr) : TermElabM (Option (Expr × Expr)) :=
  do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort (mkLevelSucc u))
    let β  ← mkFreshExprMVar (mkSort (mkLevelSucc v))
    let a ← mkFreshExprMVar α 
    let b ← mkFreshExprMVar β 
    let f := mkAppN (Lean.mkConst ``Prod.mk [u, v]) #[α, β, a, b]
    if ← isDefEq f expr
      then
        Term.synthesizeSyntheticMVarsNoPostponing
        return some (← whnf a, ← whnf b)
      else 
        return none

def split? (expr: Expr) : TermElabM (Option (Expr × Expr)) :=
    do
      let h? ← splitPProd? expr 
      let hp? ← splitProd? expr
      return h?.orElse (fun _ => hp?)

partial def unpackWeighted (expr: Expr) : TermElabM (List (Expr × Nat)) :=
    do
      match (← split? expr) with
      | some (h, t) => 
        match (← split? h) with
        | some (x, wexp) =>
            let w ←  exprNat (← whnf wexp)
            let h := (← whnf x, w)
            return h :: (← unpackWeighted t)
        | none => throwError m!"{h} is not a product (supposed to be weighted)" 
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

def packWeighted : List (Expr × Nat) →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | (x, w) :: ys => 
    do
      let t ← packWeighted ys
      let h ← mkAppM `Prod.mk #[x, ToExpr.toExpr w]
      let expr ← mkAppM `Prod.mk #[h, t]
      return expr

def ppackWeighted : List (Expr × Nat) →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | (x, w) :: ys => 
    do
      let t ← ppackWeighted ys
      let h ← mkAppM `PProd.mk #[x, ToExpr.toExpr w]
      let expr ← mkAppM `PProd.mk #[h, t]
      return expr

def lambdaPack : List Expr →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← lambdaPack ys
      let tail ← mkLambdaFVars #[x] t
      let expr ← mkAppM `PProd.mk #[x, tail]
      let expr ← whnf expr
      let expr ← reduce expr
      return expr

partial def lambdaUnpack (expr: Expr) : TermElabM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) =>
        let tt ← whnf <| mkApp t h
        let tt ← reduce tt
        let tail ←  lambdaUnpack tt
        return h :: tail
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

partial def unpack (expr: Expr) : TermElabM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) => return h :: (← unpack t) 
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

def pack : List Expr →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← pack ys
      let expr ← mkAppM `PProd.mk #[x, t]
      return expr


def packTerms : List Expr →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← packTerms ys
      if ← isProof x 
      then return t  
      else 
        let expr ← mkAppM `Prod.mk #[x, t]
        return expr

infixr:65 ":::" => PProd.mk

end ProdSeq

initialize exprDistCache : IO.Ref (HashMap Name (Expr × ExprDist)) 
                          ← IO.mkRef (HashMap.empty)

def ExprDist.save (name: Name)(es: ExprDist) : TermElabM (Unit) := do
  let lctx ← getLCtx
  let fvarIds := 
    lctx.decls.foldl (init := #[]) fun r decl? => 
    match decl? with
      | some decl => if !decl.isLet then r.push decl.fvarId else r
      | none      => r
  let fvIds ← fvarIds.filterM $ fun fid => isWhiteListed ((lctx.get! fid).userName) 
  let fvars := fvIds.map mkFVar
  Term.synthesizeSyntheticMVarsNoPostponing 
  let espair ← es.mapM (fun e => do 
       return (← Term.levelMVarToParam (← instantiateMVars e)).1)
  let es ← espair.mapM (fun e => do whnf <| ←  mkLambdaFVars fvars e)
  let varPack ← ProdSeq.lambdaPack fvars.toList
  let cache ← exprDistCache.get
  exprDistCache.set (cache.insert name (varPack, es))
  return ()

def ExprDist.load (name: Name) : TermElabM ExprDist := do
  try
    let cache ← exprDistCache.get
    match cache.find? name with
      | some (varPack, es) =>
            let fvars ← ProdSeq.lambdaUnpack varPack
            es.mapM $ fun e => do whnf <| ←  reduce (mkAppN e fvars.toArray)      
      | none => 
        throwError m!"no cached expression distribution for {name}"
  catch ex => 
    logWarning m!"Error {ex.toMessageData} while loading {name}"
    return ExprDist.empty