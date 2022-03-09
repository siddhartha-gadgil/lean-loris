import Lean.Meta
import Lean.Elab
import Std
import LeanLoris.Core
open Lean Meta Elab Term Std

open Nat

/- 
Serializing and deserializing lists of expressions, possibly with degrees.
Given a list of expressions, they are combined using `PProd` (or simply `Prod`) to get a single expression, which can be returned as an elaborator as representing a single term. The empty term is represented by the contant `()`.
A similar procedure is used to serialize (with degree) lists of terms.

Conversely, given an expression is it decomposed into a list of expressions, possibly with degrees.

The serialization is used to store distributions for intermediate steps during evolution, and also to return proofs with degrees (which are succesfully generated) for specified goals.
-/
namespace ProdSeq
/--
If an expression is a `PProd` (i.e., product of terms that may be proofs), returns the components of the product.
-/
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

/--
If an expression is a product of terms (which cannot be proofs), returns the components of the product.
-/
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

/--
If an expression is either a `PProd` (i.e., product of terms that may be proofs) or a product, returns the components.
-/
def split? (expr: Expr) : TermElabM (Option (Expr × Expr)) :=
    do
      let h? ← splitPProd? expr 
      let hp? ← splitProd? expr
      return h?.orElse (fun _ => hp?)

/--
serializes a list of (with degree) expressions using `PProd` recursively.
-/
def ppackWithDegree : List (Expr × Nat) →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | (x, deg) :: ys => 
    do
      let t ← ppackWithDegree ys
      let h ← mkAppM `PProd.mk #[x, ToExpr.toExpr deg]
      let expr ← mkAppM `PProd.mk #[h, t]
      return expr


/--
serializes a list of (with degree) expressions using products recursively - it is assumed that the expressions do not represent proofs.
-/
def packWithDegree : List (Expr × Nat) →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | (x, deg) :: ys => 
    do
      let t ← packWithDegree ys
      let h ← mkAppM `Prod.mk #[x, ToExpr.toExpr deg]
      let expr ← mkAppM `Prod.mk #[h, t]
      return expr

/--
deserializes a list of (with degree) expressions.
-/
partial def unpackWithDegree (expr: Expr) : TermElabM (List (Expr × Nat)) :=
    do
      match (← split? expr) with
      | some (h, t) => 
        match (← split? h) with
        | some (x, wexp) =>
            let deg ←  exprNat (← whnf wexp)
            let h := (← whnf x, deg)
            return h :: (← unpackWithDegree t)
        | none => throwError m!"{h} is not a product (supposed to be (with degree))" 
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

/--
serialize a list of expressions where the later ones may depend on the earlier ones; the λ of the serialization of the tail with respect to the head is appended to the head, using `PProd`.
-/
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

/--
deserialize a list of expressions where the later ones may depend on the earlier ones.
-/
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

/--
serializes a list of expressions using `PProd` recursively.
-/
def pack : List Expr →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← pack ys
      let expr ← mkAppM `PProd.mk #[x, t]
      return expr

/--
serializes a list of expressions using products recursively - it is assumed that the expressions do not represent proofs.
-/
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

/--
deserialize a list of exressions; where the serialization can use `PProd` or products.
-/
partial def unpack (expr: Expr) : TermElabM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) => return h :: (← unpack t) 
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

infixr:65 ":::" => PProd.mk

end ProdSeq

/- Saving and loading an `ExprDist` -/
initialize exprDistCache : IO.Ref (HashMap Name (Expr × ExprDist)) 
                          ← IO.mkRef (HashMap.empty)

/-- save an `ExprDist` after serializing at the given name -/
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

/-- load an `ExprDist` from the given name and deserialize -/
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