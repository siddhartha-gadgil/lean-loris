import Lean.Meta
import Lean.Elab
import Std
import Lean
open Lean Meta Elab

-- Auxiliary functions mainly from lean source for finding subexpressions

def isBlackListed  (declName : Name) : TermElabM  Bool := do
  let env ← getEnv
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRecCore env declName
  <||> isMatcherCore env declName

def isAux (declName : Name) : TermElabM  Bool := do
  let env ← getEnv
  isAuxRecursor env declName
  <||> isNoConfusion env declName
  
def isNotAux  (declName : Name) : TermElabM  Bool := do
  let nAux ← isAux declName
  return (not nAux)

def isWhiteListed (declName : Name) : TermElabM Bool := do
  let bl ← isBlackListed  declName
  return !bl

-- matching some patterns 

def existsTypeExpr? (eType: Expr) : MetaM (Option (Expr × Expr)) :=
  do 
    let eType ← whnf eType
    let u ← mkFreshLevelMVar
    let v := levelZero
    let α ← mkFreshExprMVar (mkSort u)
    let type ← mkArrow α (mkSort v)
    let β  ← mkFreshExprMVar type
    let m := mkAppN (Lean.mkConst ``Exists [u]) #[α, β]
    if ← isDefEq m eType
      then
        return some (← whnf α , ← whnf β)
      else 
        return none

@[inline] def or? (p : Expr) : Option (Expr × Expr) :=
  p.app2? ``Or

def negate (p: Expr) : MetaM Expr := do
  let p ← whnf p
  match p.not? with
  | some q => return q
  | none =>
    match p with
    | Expr.app a  b _ => mkAnd a (← mkNot b) 
    | Expr.forallE _ x b _ => 
      let type ← inferType x
      let family ← 
        withLocalDecl Name.anonymous BinderInfo.default type <| fun x =>
        do
          mkLambdaFVars #[x] (← mkNot b)
      mkAppM ``Exists #[family]
    | _ =>
      match p.and? with
      | some (l, r) => 
        mkOr (← mkNot l) (← mkNot r) 
      | none =>
      match or? p with
        | some (l, r) => 
          mkAnd (← mkNot l) (← mkNot r)
        | none =>
        match ← existsTypeExpr? p with
          | some (α, β) =>
            withLocalDecl Name.anonymous BinderInfo.default α  <| fun x =>
              do 
                let y ← mkNot (← mkApp β x)
                let y ← whnf y
                mkForallFVars #[x] y
          | none =>
            match p.iff? with
            | some (l, r) => 
                mkOr (mkAnd l (← mkNot r)) (mkAnd r (← mkNot l))
            | none =>
                mkNot p

#check mkNot

#check Expr.eq?
#check @Eq
#check Expr.and?
#check @Exists
#check mkArrow
#check mkForall