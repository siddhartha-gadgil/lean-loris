import LeanLoris.FinDist
import Lean.Meta
import Lean.Elab
import Std
open Lean
open Meta
open Elab
open Lean.Elab.Term
open Std
open Std.HashMap
open Nat

initialize defEqCount : IO.Ref (HashMap Name Nat) ← IO.mkRef <| HashMap.empty
initialize defEqTime : IO.Ref Nat ← IO.mkRef 0
initialize notBEqExpr : IO.Ref (Array (Expr × Expr)) ← IO.mkRef #[]

def defCnt : IO (Array (Name × Nat)) := do return (← defEqCount.get).toArray
def defTime : IO Nat := defEqTime.get
def notBEq : IO (Array (Expr × Expr)) := notBEqExpr.get

namespace hide

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
end hide
open hide

def wrapDefEq (fst snd : Expr) (name: Name) : TermElabM Bool := do
  let cntRef ← defEqCount.get
  let timeRef ← defEqTime.get
  let nbeq ← notBEqExpr.get
  let start ← IO.monoMsNow
  let res ← isDefEq fst snd
  let finish ← IO.monoMsNow
  defEqCount.set <| cntRef.insert name ((cntRef.findD name 0) + 1)
  defEqTime.set <| timeRef + (finish - start)
  if res && !(fst == snd) then
        let lctx ← getLCtx
        let fvarIds ← lctx.getFVarIds
        -- let fvIds ← fvarIds.filterM $ fun fid => isWhiteListed ((lctx.get! fid).userName)
        let fvars := fvarIds.map mkFVar
        Term.synthesizeSyntheticMVarsNoPostponing 
        let fst ← whnf <| ←  mkLambdaFVars fvars fst
        let snd ← whnf <| ←  mkLambdaFVars fvars snd
        notBEqExpr.set (nbeq.push (fst, snd))
  return res

-- proofs will not also be stored as terms
structure ExprDist where
  termsArr : Array (Expr × Nat)
  proofsArr: Array (Expr × Expr × Nat)  
namespace ExprDist

def empty : ExprDist := ⟨Array.empty, Array.empty⟩

def updateProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  match ← (m.proofsArr.findIdxM? <| fun (l, _, w) =>  wrapDefEq l prop `updateProofM)  with
      | some j => 
          let (l, p, w) := m.proofsArr.get! j
          if w ≤ d then return m 
          else return ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updateTermM(m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => wrapDefEq t x `updateTermM) with
      | some j =>
        let (t, w) := m.termsArr.get! j 
        if w ≤ j then return m
        else return ⟨m.termsArr.set! j (x, d), m.proofsArr⟩
      | none => 
          return ⟨m.termsArr.push (x, d), m.proofsArr⟩

def updateExprM
    (m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    if ← isProof x then
      let prop ← whnf (← inferType x)
      Term.synthesizeSyntheticMVarsNoPostponing
      updateProofM m prop x d
    else 
      updateTermM m x d

def pushTerm(m: ExprDist)(x: Expr)(d: Nat) : ExprDist :=
  ⟨m.termsArr.push (x, d), m.proofsArr⟩

def pushProof(m: ExprDist)(prop x: Expr)(d: Nat) : ExprDist :=
  ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updatedProofM?(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM (Option ExprDist) := do
  match ← (m.proofsArr.findIdxM? <| fun (l, _, w) =>  wrapDefEq l prop `updatedProofM?)  with
      | some j => 
          let (l, p, w) := m.proofsArr.get! j
          if w ≤ d then return none
          else return some ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return some ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updatedTermM?(m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => wrapDefEq t x `updatedTermM?) with
      | some j =>
        let (t, w) := m.termsArr.get! j 
        if w ≤ j then return none
        else return some ⟨m.termsArr.set! j (x, d), m.proofsArr⟩
      | none => 
          return some ⟨m.termsArr.push (x, d), m.proofsArr⟩

def updatedExprM?
    (m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    if ← isProof x then
      let prop ← whnf (← inferType x)
      Term.synthesizeSyntheticMVarsNoPostponing
      updatedProofM? m prop x d
    else 
      updatedTermM? m x d


def mapM(dist: ExprDist)(f: Expr → TermElabM Expr) : TermElabM ExprDist := do
  let termsArrBase ← dist.termsArr.mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  termsArrBase.foldlM (fun  dist (e, n) => 
    do dist.updateExprM e n) empty

def mergeM(fst snd: ExprDist) : TermElabM ExprDist := do
    logInfo m!"merging; time: {← IO.monoMsNow}; sizes: ({fst.termsArr.size}, {fst.proofsArr.size}) ({snd.termsArr.size}, {snd.proofsArr.size})"
    let mut dist := fst
    let mut ⟨fstTerms, fstProofs⟩ := fst
    let mut ⟨sndTerms, sndProofs⟩ := ExprDist.empty
    for (prop, x, d) in snd.proofsArr do
      match ← (fstProofs.findIdxM? <| fun (l, _, w) =>  wrapDefEq l prop `mergeM)  with
      | some j => 
          let (l, p, w) := fstProofs.get! j
          if w ≤ d then ()
          else 
           fstProofs := fstProofs.eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArr do
      match ← (fstTerms.findIdxM? <| fun (t, w) =>  wrapDefEq t x `mergeM)  with
      | some j => 
          let (t, w) := fstTerms.get! j
          if w ≤ d then ()
          else 
           fstTerms := fstTerms.eraseIdx j 
           sndTerms := sndTerms.push (x, d)
      | none => 
          sndTerms := sndTerms.push (x, d)
    let res := ⟨fstTerms ++ sndTerms, fstProofs ++ sndProofs⟩
    logInfo m!"merged arrays obtained; time: {← IO.monoMsNow}; size: {fstTerms.size + sndTerms.size}; {fstProofs.size + sndProofs.size}"
    return res

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeM⟩

def fromTermsM(dist: FinDist Expr): TermElabM ExprDist := do
  dist.foldM  (fun m e n => m.updateExprM e n) ExprDist.empty

def fromArray(arr: Array (Expr× Nat)): TermElabM ExprDist :=
  arr.foldlM (fun dist (e, w) => ExprDist.updateExprM dist e w) ExprDist.empty

def existsM(dist: ExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      dist.proofsArr.anyM <| fun (l, _, w) => 
              do pure (decide <| w ≤ weight) <&&> wrapDefEq l prop `existsM
    else 
      dist.termsArr.anyM <| fun (t, w) => 
              do pure (decide <| w ≤ weight) <&&> wrapDefEq t elem `existsM

def existsPropM(dist: ExprDist)(prop: Expr)(weight: Nat) : TermElabM Bool :=
    dist.proofsArr.anyM <| fun (l, _, w) => 
              do pure (decide <| w ≤ weight) <&&> wrapDefEq l prop `existsMProp

def terms(dist: ExprDist) : FinDist Expr := 
      FinDist.fromArray dist.termsArr

def allTerms(dist: ExprDist) : FinDist Expr := 
      FinDist.fromArray (dist.termsArr ++ 
          (dist.proofsArr.map <| fun (_, t, w) => (t, w)))

def allSorts(dist: ExprDist) : TermElabM (FinDist Expr) := do
  let types ←  dist.termsArr.filterM <| fun (e, w) => do
          (← inferType e).isSort
  let props := dist.proofsArr.map <| fun (l, _, w) => (l, w)
  return FinDist.fromArray <| types ++ props

def getProof?(dist: ExprDist)(prop: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  let opt ←  dist.proofsArr.findM? <| fun (l, p, w) => isDefEq l prop
  return opt.map <| fun (_, p, w) => (p, w)

def getTerm?(dist: ExprDist)(elem: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  dist.termsArr.findM? <| fun (t, w) => isDefEq t elem

def getGoals(dist: ExprDist)(goals : Array Expr) : TermElabM (Array (Expr × Nat )) := 
  do
    goals.filterMapM <| fun g => do 
      let wpf ← dist.getProof? g
      let wt ← dist.getTerm? g
      return wpf.orElse (fun _ => wt)

def findD(dist: ExprDist)(elem: Expr)(default: Nat) : TermElabM Nat := do
  match ← getTerm? dist elem with
  | some (t, w) => pure w
  | none => pure default

end ExprDist

structure HashExprDist where
  termsMap : FinDist UInt64
  propsMap : FinDist UInt64

def ExprDist.hashDist(expr: ExprDist) : HashExprDist := 
  { termsMap := FinDist.fromArray (expr.termsArr.map <| fun (e, w) => (hash e, w)),
    propsMap := FinDist.fromArray (expr.proofsArr.map <| fun (l, e, w) => (hash e, w)) }

def HashExprDist.existsM(dist: HashExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      dist.propsMap.exists (hash prop) weight
    else 
      dist.termsMap.exists (hash elem) weight
