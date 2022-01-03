import Lean.Meta
import Lean.Elab
import Std
open Lean
open Meta
open Lean.Elab.Term
open Std
open Std.HashMap
open Nat

abbrev ExprDist := HashMap Expr Nat

structure Bounds where
  depth: Nat
  card : Nat 

structure GenDist where
  depth: Nat
  card : Nat
  exprDist : ExprDist

def Evolution : Type := (init: ExprDist) → Bounds → (memo: List GenDist) → GenDist

def trivialEvolution : Evolution := fun init bds _ => GenDist.mk bds.depth bds.card  init

def RecEvolver : Type := (init: ExprDist) → Bounds → (memo: List GenDist) → (evo: Evolution) → GenDist

instance : Inhabited Evolution := ⟨trivialEvolution⟩

partial def RecEvolver.diag(recEv: RecEvolver) : Evolution :=
        fun init bds memo => recEv init bds memo (diag recEv)

-- Auxiliary functions mainly from lean source for subexpressions

def isBlackListed (env: Environment) (declName : Name) : IO  Bool := do
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRecCore env declName
  <||> isMatcherCore env declName

def isAux (env: Environment) (declName : Name) : IO  Bool := do
  isAuxRecursor env declName
  <||> isNoConfusion env declName
  
def isNotAux (env: Environment) (declName : Name) : IO  Bool := do
  let nAux ← isAux env declName
  return (not nAux)

def isWhiteListed (env: Environment)(declName : Name) : IO Bool := do
  let bl ← isBlackListed env declName
  return !bl

-- Basic functions for generation

-- (optional) function application with unification
def applyOpt (f x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x] none (explicit := false) (ellipsis := false)
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then return some expr
      else return none
    catch e =>
      return none

-- (optional) function application with unification given name of function
def nameApplyOpt (f: Name) (x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        return some expr
      else
      Elab.logWarning m!"not type correct : {expr} = {f} ({x})" 
      return none
    catch e =>
        -- Elab.logInfo m!"failed from name, arg : 
        --     {f} at {x} with type {← inferType x}"
      return none

-- (optional) function application with unification given name of function and a pair of arguments
def nameApplyPairOpt (f: Name) (x y: Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x, y]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        return some expr
      else
      Elab.logWarning m!"not type correct : {expr} = {f}({x}, {y})" 
      return none
    catch e =>
        -- Elab.logInfo m!"failed from name, arg : 
        --     {f} at {x}, {y} with type {← inferType x}"
      return none


-- copied from lean4 source code and modified; optionally returns proof that
-- a rewritten expression is equal to the original one.
def rewriteProof (e: Expr) (heq : Expr) (symm : Bool := false) : MetaM (Option Expr) :=
  do
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    match heqType.eq? with
    | none => none
    | some (α , lhs, rhs) =>
    let heqType := if symm then ← mkEq rhs lhs else heqType
    let hep := if symm then mkEqSymm heq else heq
    if lhs.getAppFn.isMVar then none
    else
    let e ← instantiateMVars e
    let eAbst ←  kabstract e lhs
    if !eAbst.hasLooseBVars then none
    else
    let eNew := eAbst.instantiate1 rhs
    let eNew ← instantiateMVars eNew
    let eEqE ← mkEq e e
    let eEqEAbst := mkApp eEqE.appFn! eAbst
    let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst
    if !(← isTypeCorrect motive) then none
    else            
    let eqRefl ← mkEqRefl e
    let eqPrf ← mkEqNDRec motive eqRefl heq
    return some eqPrf

-- transports a term using equlity if its type can be rewritten
def rwPushOpt(e : Expr) (heq : Expr) 
      (symm : Bool := false): MetaM (Option Expr) :=
  do
    let t ← inferType e
    let pfOpt ← rewriteProof t heq symm
    match pfOpt with
    | none => return none
    | some pf =>
      try
        let expr ← mkAppM ``Eq.mp #[pf, e]
        let exprType ← inferType expr
        if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  
        then return some expr
        else return none
      catch _ => 
        return none

-- (optional) congrArg for an equality
def eqCongrOpt (f: Expr)(eq : Expr) : MetaM (Option Expr) :=
  do
    try
      let expr ← mkAppM ``congrArg #[f, eq]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then return some expr
      else 
        return none
    catch e => 
      return none 
