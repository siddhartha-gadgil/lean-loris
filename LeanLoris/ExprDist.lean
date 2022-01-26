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
  terms : FinDist Expr
  proofs: HashMap Expr (Expr × Nat)  
namespace ExprDist

def empty : ExprDist := ⟨HashMap.empty, HashMap.empty⟩

def updateExprM
    (m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    if ← isProof x then
      let prop ← whnf (← inferType x)
      Term.synthesizeSyntheticMVarsNoPostponing
      match m.proofs.find? prop with
      | some (p, n) =>
        if d < n then
          return ⟨(m.terms.erase p).insert x d, m.proofs.insert prop (x, d)⟩
        else
          return m 
      | none => 
        return ⟨m.terms.insert x d, m.proofs.insert prop (x, d)⟩
    else 
      match m.terms.find? x with
      | some v => if d < v then return ⟨m.terms.insert x d, m.proofs⟩ else m
      | none => return ⟨m.terms.insert x d, m.proofs⟩

def mapM(dist: ExprDist)(f: Expr → TermElabM Expr) : TermElabM ExprDist := do
  let pfList ← dist.proofs.toList.mapM <| fun (p, (e, n)) => do
    let e ← f e
    let p ← f p
    return (p, (e, n))
  let pfMap : HashMap Expr (Expr × Nat) := 
      pfList.foldl (fun m (p, (e, n)) => m.insert p (e, n)) HashMap.empty
  return ⟨← dist.terms.mapM f, pfMap⟩

def mergeM(fst snd: ExprDist) : TermElabM ExprDist := do
    let mut dist := fst
    for (key, val) in snd.terms.toArray do
      dist ←  dist.updateExprM key val
    return dist

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeM⟩

def fromTerms(dist: FinDist Expr): TermElabM ExprDist := do
  dist.foldM  (fun m e n => m.updateExprM e n) ExprDist.empty

def existsM(dist: ExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← whnf (← inferType elem)
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← dist.proofs.find? prop with
      | some (p, n) =>
        return n ≤ weight
      | none => 
        return false
    else 
      return dist.terms.exists elem weight

end ExprDist
