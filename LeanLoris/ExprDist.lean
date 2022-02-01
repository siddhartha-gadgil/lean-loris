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
  termsMap : HashMap Expr  Nat
  proofsMap: HashMap Expr (Expr × Nat)  
namespace ExprDist

def empty : ExprDist := ⟨HashMap.empty, HashMap.empty⟩

def updateProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  match ← (m.proofsMap.find? prop)  with
      | some (p, w) => 
          if w ≤ d then return m 
          else return ⟨m.termsMap, m.proofsMap.insert prop (x, d)⟩
      | none => 
        return ⟨m.termsMap, m.proofsMap.insert prop (x, d)⟩

def updateTermM(m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    match ← (m.termsMap.find? x) with
      | some w =>
        if w ≤ d then return m
        else return ⟨m.termsMap.insert x d, m.proofsMap⟩
      | none => 
          return ⟨m.termsMap.insert x d, m.proofsMap⟩

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
  ⟨m.termsMap.insert x d, m.proofsMap⟩

def pushProof(m: ExprDist)(prop x: Expr)(d: Nat) : ExprDist :=
  ⟨m.termsMap, m.proofsMap.insert prop (x, d)⟩

def updatedProofM?(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM (Option ExprDist) := do
  match ← (m.proofsMap.find? prop)  with
      | some (p, w) => 
          if w ≤ d then return none
          else return some ⟨m.termsMap, m.proofsMap.insert prop (x, d)⟩
      | none => 
        return some ⟨m.termsMap, m.proofsMap.insert prop (x, d)⟩

def updatedTermM?(m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    match ← (m.termsMap.find? x) with
      | some w =>
        if w ≤ d then return none
        else return some ⟨m.termsMap.insert x d, m.proofsMap⟩
      | none => 
          return some ⟨m.termsMap.insert x d, m.proofsMap⟩
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
  let termsArrBase ← dist.termsMap.toArray.mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  termsArrBase.foldlM (fun  dist (e, n) => 
    do dist.updateExprM e n) empty

def mergeM(fst snd: ExprDist) : TermElabM ExprDist := do
    let mut ⟨distTerms, distProofs⟩ := fst
    for (prop, x, d) in snd.proofsMap.toArray do
      match ← (fst.proofsMap.find? prop)  with
      | some (p, w) => 
          if w ≤ d then ()
          else 
           distProofs := distProofs.insert prop (x, d)
      | none => 
          distProofs := distProofs.insert prop (x, d)
    for (x, d) in snd.termsMap.toArray do
      match ← (fst.termsMap.find? x)  with
      | some w => 
          if w ≤ d then ()
          else 
           distTerms := distTerms.insert x d
      | none => 
          distTerms := distTerms.insert x d
    return ⟨distTerms, distProofs⟩

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeM⟩

def fromTermsM(dist: FinDist Expr): TermElabM ExprDist := do
  dist.foldM  (fun m e n => m.updateExprM e n) ExprDist.empty

def existsM(dist: ExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      match dist.proofsMap.find? prop with
        | some (p, w) => return w ≤ weight 
        | none => return false
    else 
      match dist.termsMap.find? elem with
        | some w => return w ≤ weight
        | none => return false 

def existsPropM(dist: ExprDist)(prop: Expr)(weight: Nat) : TermElabM Bool :=
    match dist.proofsMap.find? prop with
        | some (p, w) => return w ≤ weight 
        | none => return false

def terms(dist: ExprDist) : FinDist Expr := 
      dist.termsMap

def allTerms(dist: ExprDist) : FinDist Expr := 
      FinDist.fromArray (dist.termsMap.toArray ++ 
          (dist.proofsMap.toArray.map <| fun (_, t, w) => (t, w)))

def allSorts(dist: ExprDist) : TermElabM (FinDist Expr) := do
  let types ←  dist.termsMap.toArray.filterM <| fun (e, w) => do
          (← inferType e).isSort
  let props := dist.proofsMap.toArray.map <| fun (l, _, w) => (l, w)
  return FinDist.fromArray <| types ++ props

def termsArr(dist: ExprDist) : Array (Expr × Nat) := 
      dist.termsMap.toArray

def proofsArr(dist: ExprDist) : Array (Expr × Expr × Nat) := 
      dist.proofsMap.toArray

end ExprDist
