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

def Array.oddEven {α : Type}(arr: Array α) : (Array α) × (Array α) :=
  let (odds, evens, _) : (Array α) × (Array α) × Bool := arr.foldl ( fun (arr1, arr2, b) x =>
      if b then (arr1.push x, arr2, !b) else (arr1, arr2.push x, !b) ) (#[], #[], false) 
  (odds, evens)

#eval #[3, 7, 12, 13, 14, 1, 4].oddEven

-- proofs will not also be stored as terms
structure ExprDist where
  termsArr : Array (Expr × Nat)
  proofsArr: Array (Expr × Expr × Nat)  
namespace ExprDist

def empty : ExprDist := ⟨Array.empty, Array.empty⟩

def updateProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  match ← (m.proofsArr.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := m.proofsArr.get! j
          if w ≤ d then return m 
          else return ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updateTermM(m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => isDefEq t x) with
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
  match ← (m.proofsArr.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := m.proofsArr.get! j
          if w ≤ d then return none
          else return some ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return some ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updatedTermM?(m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => isDefEq t x) with
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
    let termIndexMatchesAux :=  snd.termsArr.map ( fun (x, _) =>
        (Task.spawn (fun _ =>    (fst.termsArr.findIdxM? <| fun (t, w) =>  isDefEq t x))
        Task.Priority.dedicated 
        ))
    let proofIndexMatchesAux := snd.proofsArr.map ( fun (prop , _, _) =>
        Task.spawn (fun _ =>    (fst.proofsArr.findIdxM? <| fun (l, _, w) =>  isDefEq l prop))
        Task.Priority.dedicated
        )
    logInfo m!"created index find tasks; time: {← IO.monoMsNow}"
    let termIndexMatches ← termIndexMatchesAux.mapM <| fun b => b.get
    let proofIndexMatches ← proofIndexMatchesAux.mapM <| fun b => b.get
    logInfo m!"obtained optional indices; time: {← IO.monoMsNow}"
    for ((prop, x, d), opt) in (snd.proofsArr.zip (proofIndexMatches)) do
      match opt  with
      | some j => 
          let (l, p, w) := fstProofs.get! j
          if w ≤ d then ()
          else 
           fstProofs := fstProofs.set! j (prop, x, d) 
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for ((x, d), opt) in (snd.termsArr.zip termIndexMatches) do
      match opt  with
      | some j => 
          let (t, w) := fstTerms.get! j
          if w ≤ d then ()
          else 
           fstTerms := fstTerms.set! j (x, d) 
      | none => 
          sndTerms := sndTerms.push (x, d)
    let res := ⟨fstTerms ++ sndTerms, fstProofs ++ sndProofs⟩
    logInfo m!"merged arrays obtained; time: {← IO.monoMsNow}; size: {fstTerms.size + sndTerms.size}; {fstProofs.size + sndProofs.size}"
    return res

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeM⟩

def fromTermsM(dist: FinDist Expr): TermElabM ExprDist := do
  dist.foldM  (fun m e n => m.updateExprM e n) ExprDist.empty

partial def fromArray(arr: Array (Expr× Nat)): TermElabM ExprDist :=
  if arr.size < 10 then
    arr.foldlM (fun dist (e, w) => ExprDist.updateExprM dist e w) ExprDist.empty
  else do
    let (odds, evens) := arr.oddEven
    let oddDistT := Task.spawn fun _ => fromArray odds
    let evenDistT := Task.spawn fun _ => fromArray evens  
    mergeM (← oddDistT.get) (← evenDistT.get)

def existsM(dist: ExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      dist.proofsArr.anyM <| fun (l, _, w) => 
              do pure (decide <| w ≤ weight) <&&> isDefEq l prop
    else 
      dist.termsArr.anyM <| fun (t, w) => 
              do pure (decide <| w ≤ weight) <&&> isDefEq t elem

def existsPropM(dist: ExprDist)(prop: Expr)(weight: Nat) : TermElabM Bool :=
    dist.proofsArr.anyM <| fun (l, _, w) => 
              do pure (decide <| w ≤ weight) <&&> isDefEq l prop

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
