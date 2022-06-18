import Lean.Meta
import Lean.Elab
import Std
import Lean
open Lean Meta Elab Nat Term Std

/- Mostly Meta level (including Elab level) utility functions -/

/-- ≤  an optional bound -/
def leqOpt(x: Nat)(bd: Option Nat) : Bool :=
  match bd with
  | none => true
  | some b => x ≤ b

initialize contextCache : IO.Ref (Option (Simp.Context)) ← IO.mkRef none

def getContext : MetaM Simp.Context := do
  let cache ← contextCache.get
  match cache with
  | none =>
    let ctx ← Simp.Context.mkDefault
    contextCache.set (some ctx)
    pure ctx
  | some c => pure c

initialize simplifyCache : IO.Ref (HashMap Expr Expr) ← IO.mkRef HashMap.empty

def Lean.Expr.simplify(e: Expr) : MetaM Expr := do 
  let cache ← simplifyCache.get
  match cache.find? e with
  | none => 
    let r ← simp e (← Simp.Context.mkDefault)
    simplifyCache.set (cache.insert e r.expr)
    return r.expr
  | some expr => return expr

/- from the lean source (with minor modifications) -/

def isBlackListed  (declName : Name) : MetaM  Bool := do
  let env ← getEnv
  return (declName.isInternal
  || isAuxRecursor env declName
  || isNoConfusion env declName
  || isRecCore env declName
  || isMatcherCore env declName)

def isAux (declName : Name) : MetaM  Bool := do
  let env ← getEnv
  return (isAuxRecursor env declName
          || isNoConfusion env declName)
  
def isNotAux  (declName : Name) : MetaM  Bool := do
  let nAux ← isAux declName
  return (not nAux)

def isWhiteListed (declName : Name) : MetaM Bool := do
  let bl ← isBlackListed  declName
  return !bl

/-- natural number from expression built from `Nat.zero` and `Nat.succ` -/
partial def exprNat : Expr → TermElabM Nat := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp := mkApp (mkConst ``Nat.succ) mvar
    if ← isDefEq sExp expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      let prev ← exprNat (← whnf mvar)
      return succ prev
    else 
    if ← isDefEq (mkConst `Nat.zero) expr then
      return zero
    else
      throwError m!"{expr} not a Nat expression"

/-- formatted view of an expression -/
def view(expr: Expr): MetaM String := do
  let stx ← PrettyPrinter.delab  expr
  let fmt ← PrettyPrinter.ppTerm stx
  return fmt.pretty

/-- optionally infer type of expression -/
def inferType?(e: Expr) : MetaM (Option Expr) := do
  try
    let type ← inferType e
    return some type
  catch _ => return none

/- Matching some patterns of expressions; using this to negate -/

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

/-- negate an expression -/
def negate (p: Expr) : MetaM Expr := do
  let p ← whnf p
  match p.not? with
  | some q => return q
  | none => 
    match p with
    | Expr.app a  b _ => return (mkAnd a (mkNot b)) 
    | Expr.forallE _ x b _ => 
      let type ← inferType x
      let family ← 
        withLocalDecl Name.anonymous BinderInfo.default type <| fun x =>
        do
          mkLambdaFVars #[x] (mkNot b)
      mkAppM ``Exists #[family]
    | _ => 
      match p.and? with
      | some (l, r) => 
        return (mkOr (mkNot l) (mkNot r)) 
      | none => 
        match or? p with
        | some (l, r) => 
          return (mkAnd (mkNot l) (mkNot r))
        | none => 
          match ← existsTypeExpr? p with
          | some (α, β) =>
            withLocalDecl Name.anonymous BinderInfo.default α  <| fun x =>
              do 
                let y := mkNot (mkApp β x)
                let y ← whnf y
                mkForallFVars #[x] y
          | none => 
            match p.iff? with
            | some (l, r) => 
                return (mkOr (mkAnd l (mkNot r)) (mkAnd r (mkNot l)))
            | none =>
                return (mkNot p)
