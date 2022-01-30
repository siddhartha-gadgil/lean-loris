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

-- proofs will not also be stored as terms
structure ExprDist where
  termsArr : Array (Expr × Nat)
  proofsArr: Array (Expr × Expr × Nat)  
namespace ExprDist

def empty : ExprDist := ⟨Array.empty, Array.empty⟩

def updateExprM
    (m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    if ← isProof x then
      let prop ← whnf (← inferType x)
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← (m.proofsArr.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := m.proofsArr.get! j
          if w ≤ d then return m 
          else return ⟨m.termsArr, m.proofsArr.insertAt j (prop, x, d)⟩
      | none => 
        return ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩
    else 
      match ← (m.termsArr.findIdxM? <| fun (t, w) => isDefEq t x) with
      | some j =>
        let (t, w) := m.termsArr.get! j 
        if w ≤ j then return m
        else return ⟨m.termsArr.insertAt j (x, d), m.proofsArr⟩
      | none => 
          return ⟨m.termsArr.push (x, d), m.proofsArr⟩

def mapM(dist: ExprDist)(f: Expr → TermElabM Expr) : TermElabM ExprDist := do
  let termsArrBase ← dist.termsArr.mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  termsArrBase.foldlM (fun  dist (e, n) => 
    do dist.updateExprM e n) empty

def mergeM(fst snd: ExprDist) : TermElabM ExprDist := do
    let mut dist := fst
    let mut ⟨fstTerms, fstProofs⟩ := fst
    let mut ⟨sndTerms, sndProofs⟩ := ExprDist.empty
    for (prop, x, d) in snd.proofsArr do
      match ← (fstProofs.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := fstProofs.get! j
          if w ≤ d then ()
          else 
           fstProofs := fstProofs.eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArr do
      match ← (fstTerms.findIdxM? <| fun (t, w) =>  isDefEq t x)  with
      | some j => 
          let (t, w) := fstTerms.get! j
          if w ≤ d then ()
          else 
           fstTerms := fstTerms.eraseIdx j 
           sndTerms := sndTerms.push (x, d)
      | none => 
          sndTerms := sndTerms.push (x, d)
    return ⟨fstTerms ++ sndTerms, fstProofs ++ sndProofs⟩

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeM⟩

def fromTermsM(dist: FinDist Expr): TermElabM ExprDist := do
  dist.foldM  (fun m e n => m.updateExprM e n) ExprDist.empty

def existsM(dist: ExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      dist.proofsArr.anyM <| fun (l, _, w) => 
              do pure (decide <| w ≤ weight) <&&> isDefEq l prop
    else 
      dist.termsArr.anyM <| fun (t, w) => 
              do pure (decide <| w ≤ weight) <&&> isDefEq t elem

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
