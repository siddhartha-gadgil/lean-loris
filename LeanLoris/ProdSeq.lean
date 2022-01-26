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
      let hOpt ← splitPProd? expr 
      let hpOpt ← splitProd? expr
      return hOpt.orElse (fun _ => hpOpt)

partial def unpackWeighted (expr: Expr) : TermElabM (List (Expr × Nat)) :=
    do
      match (← split? expr) with
      | some (h, t) => 
        match (← split? h) with
        | some (x, wexp) =>
            -- logInfo m!"weight: {← whnf wexp} with type {← whnf (← inferType wexp)}"
            let w ←  exprNat (← whnf wexp)
            let h := (← whnf x, w)
            h :: (← unpackWeighted t)
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

def lambdaPack : List Expr →  MetaM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← lambdaPack ys
      let tail ← mkLambdaFVars #[x] t
      let expr ← mkAppM `PProd.mk #[x, tail]
      return expr

partial def lambdaUnpack (expr: Expr) : TermElabM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) =>
        let tt ← whnf <| mkApp t h
        let tail ←  lambdaUnpack tt
        h :: tail
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

syntax (name:= roundtripWtd) "roundtrip-weighted!" term : term
@[termElab roundtripWtd] def roundtripWtdImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(roundtrip-weighted! $t) => 
    do
      let expr ← elabTerm t none
      let l ← unpackWeighted expr
      -- logInfo m!"unpacked {l.length}"
      -- for (e, w) in l do
      --   logInfo m!"{← whnf e} : {w}"
      let e ← ppackWeighted l
      let ll ← unpackWeighted e
      let ee ← packWeighted ll
      return ee
  | _ => throwIllFormedSyntax

#eval roundtrip-weighted! (((), 9), (2, 7), ("Hello", 12), ())

partial def unpack (expr: Expr) : TermElabM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) => h :: (← unpack t) 
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

syntax (name := prodHead) "prodHead!" term : term
@[termElab prodHead] def prodHeadImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(prodHead! $t) => 
    do
      let expr ← elabTerm t none
      let hOpt ← splitPProd? expr 
      let hpOpt ← splitProd? expr
      match (hOpt.orElse (fun _ => hpOpt)) with
      | some (h, t) => return h
      | none => throwAbortTerm    
  | _ => throwIllFormedSyntax

#eval prodHead! (10, 12, 15, 13)


syntax (name := prodlHead) "prodlHead!" term : term
@[termElab prodlHead] def prodlHeadImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(prodlHead! $t) => 
    do
      let expr ← elabTerm t none
      let l ← try 
        unpack expr
        catch exc => throwError m!"Error {exc.toMessageData} while unpacking {expr}"
      return l.head!   
  | _ => throwIllFormedSyntax

#eval prodlHead! (3, 10, 12, 13, ())

syntax (name:= roundtrip) "roundtrip!" term : term
@[termElab roundtrip] def roundtripImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(roundtrip! $t) => 
    do
      let expr ← elabTerm t none
      let l ← unpack expr
      let e ← pack l
      let ll ← unpack e
      let ee ← pack ll
      return ee
  | _ => throwIllFormedSyntax

syntax (name:= justterms) "terms!" term : term
@[termElab justterms] def justtermsImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(terms! $t) => 
    do
      let expr ← elabTerm t none
      let l ← unpack expr
      let e ← packTerms l
      return e
  | _ => throwIllFormedSyntax

#check roundtrip! (3, 10, "twelve", 13, ())

infixr:65 ":::" => PProd.mk

#check roundtrip!  (rfl : 1 = 1) ::: "this" ::: 4 ::: 3 ::: ()

#eval terms! "hello" ::: (rfl : 1 = 1) ::: "this" ::: 4 ::: 3 ::: ()

declare_syntax_cat expr_dist 

syntax exprWt := "(" term "," num ")"
syntax exprWtList := "%{" exprWt,* "}"
syntax exprWtList : expr_dist

def parseExprMap : Syntax → TermElabM (Array (Expr × Nat))
  | `(expr_dist|%{$[$xs:exprWt],*}) =>
    do
          let m : Array (Expr × Nat) ←  xs.mapM (fun s => do
              match s with 
              | `(exprWt|($x:term , $n:numLit)) => 
                  let expr ← elabTerm x none
                  return (expr, (Syntax.isNatLit? n).get!)
              | _ =>
                throwError m!"{s} is not a valid exprWt"
              )
          m
  | _ => throwIllFormedSyntax

syntax (name:= exprDistPack) "packdist!" expr_dist : term
@[termElab exprDistPack] def exprDistPackImpl : TermElab := fun stx _ =>
    match stx with 
    | `(packdist! $s:expr_dist) => 
        do
          let m : Array (Expr × Nat) ←  parseExprMap s
          packWeighted m.toList
    | _ => throwIllFormedSyntax

#eval packdist! %{(1, 2), ("Hello", 4)}
#check packdist! %{(1, 2), ("Hello", 4)}

#reduce (fun x y : Nat => packdist!%{ (1, 2), ("Hello", 4), (x + 1 + y, 3)}) 4 7

declare_syntax_cat expr_list
syntax "%[" term,* "]" : expr_list

def parseExprList : Syntax → TermElabM (Array Expr)
  | `(expr_list|%[$[$xs],*]) =>
    do
          let m : Array Expr ←  xs.mapM <| fun s => elabTerm s none
          return m
  | _ => throwIllFormedSyntax

syntax (name:= exprPack) "pack!" expr_list : term
@[termElab exprPack] def exprPackImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(pack! $s:expr_list) => 
    do
          let m : Array (Expr) ←  parseExprList s
          pack m.toList
  | _ => throwIllFormedSyntax

#check pack! %[(1, 2), 3, ("Hello", 4), "over here"]

declare_syntax_cat name_dist
syntax nameWt := "(" ident "," num ")"
syntax nameWtList := "!{" nameWt,* "}"
syntax nameWtList : name_dist

def parseNameMap : Syntax → TermElabM (Array (Name × Nat))
  | `(name_dist|!{$[$xs:nameWt],*}) =>
    do
          let m : Array (Name × Nat) ←  xs.mapM (fun s => do
              match s with 
              | `(nameWt|($x:ident, $n:numLit)) =>                  
                  return (x.getId, (Syntax.isNatLit? n).get!)
              | _ =>
                throwError m!"{s} is not a valid nameWt"
              )
          m
  | _ => throwIllFormedSyntax

syntax (name:= constpack) "const!" name_dist : term
@[termElab constpack] def constpackImpl : TermElab := fun stx _ =>
    match stx with 
    | `(const! $s:name_dist) => 
        do
          let m : Array (Name × Nat) ←  parseNameMap s
          let c := m.map (fun (n, w) => (mkConst n, w))
          packWeighted c.toList
    | _ => throwIllFormedSyntax

#check const! !{(Nat.add, 2), (Nat.zero, 4)}


end ProdSeq

initialize exprDistCache : IO.Ref (HashMap Name (Expr × ExprDist)) 
                          ← IO.mkRef (HashMap.empty)

def ExprDist.save (es: ExprDist)(name: Name) : TermElabM (Unit) := do
  let lctx ← getLCtx
  let fvarIds ← lctx.getFVarIds
  let fvIds ← fvarIds.filterM $ fun fid => isWhiteListed ((lctx.get! fid).userName) 
  let fvars := fvIds.map mkFVar
  Term.synthesizeSyntheticMVarsNoPostponing 
  let espair ← es.mapM (fun e => do (← Term.levelMVarToParam (← instantiateMVars e)).1)
  let es ← espair.mapM (fun e => do whnf <| ←  mkLambdaFVars fvars e)
  logInfo m!"saving relative to: {fvars}"
  let varPack ← ProdSeq.lambdaPack fvars.toList
  let cache ← exprDistCache.get
  exprDistCache.set (cache.insert name (varPack, es))
  return ()

def ExprDist.load (name: Name) : TermElabM (ExprDist) := do
  let cache ← exprDistCache.get
  match cache.find? name with
  | some (varPack, es) =>
        let fvars ← ProdSeq.lambdaUnpack varPack
        logInfo m!"loading relative to: {fvars}"
        es.mapM $ fun e => reduce (mkAppN e fvars.toArray)
  | none => throwError m!"no cached expression distribution for {name}"
