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

structure ExprDist where
  termsArr : Array (Expr × Nat)
  proofsArr: Array (Expr × Expr × Nat)  
namespace ExprDist

def empty : ExprDist := ⟨Array.empty, Array.empty⟩

-- TODO: purge on adding 
def updateExprM
    (m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    if ← isProof x then
      let prop ← whnf (← inferType x)
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← (m.proofsArr.findM? <| fun (l, _, w) => 
              do pure (decide <| w ≤ d) <&&> isDefEq l prop)  with
      | some (l, p, n) =>
          return m
      | none => 
        let termsArr ←  m.termsArr.filterM <| fun (t, w) => 
              do w ≤ d ||  !(← isDefEq t x)
        let proofsArr ←  m.proofsArr.filterM <| fun (l, _, w) => 
              do w ≤ d ||  !(← isDefEq l prop)
        return ⟨termsArr.push (x, d), proofsArr.push (prop, x, d)⟩
    else 
      match ← (m.termsArr.findM? <| fun (t, w) => 
              do pure (decide <| w ≤ d) <&&> isDefEq t x) with
      | some v => return m
      | none => 
          let termsArr ←  m.termsArr.filterM <| fun (t, w) => 
              do w ≤ d ||  !(← isDefEq t x)
          return ⟨termsArr.push (x, d), m.proofsArr⟩

def mapM(dist: ExprDist)(f: Expr → TermElabM Expr) : TermElabM ExprDist := do
  let termsArrBase ← dist.termsArr.mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  termsArrBase.foldlM (fun  dist (e, n) => 
    do dist.updateExprM e n) empty

def mergeM(fst snd: ExprDist) : TermElabM ExprDist := do
    let mut dist := fst
    for (key, val) in snd.termsArr do
      dist ←  dist.updateExprM key val
    return dist

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

def terms(dist: ExprDist) : FinDist Expr := FinDist.fromArray dist.termsArr

end ExprDist
