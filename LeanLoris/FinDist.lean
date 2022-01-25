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

/- 
  Hashmaps for distributions; especially for expressions; with basic map, filter methods
  including Mondaic forms
-/
abbrev FinDist (α : Type)[Hashable α][BEq α] := HashMap α Nat 



abbrev NameDist := FinDist Name

namespace FinDist

def empty{α : Type} [Hashable α][BEq α] : FinDist α := HashMap.empty

def merge{α : Type}[Hashable α][BEq α] 
    (fst: FinDist α)(snd: FinDist α) : FinDist α  := Id.run do
  let mut min := fst
  for (key, val) in snd.toArray do
    match min.find? key with
    | some v =>
      if val < v then
        min := min.insert key val
    | none => 
        min := min.insert key val
  return min

instance {α : Type}[Hashable α][BEq α ]: Append <| FinDist α  := 
                                  ⟨fun fst snd => fst.merge snd⟩


def map{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (dist: FinDist α)(f: α → β ) : FinDist β   := 
  dist.toArray.foldl (fun map (key, val) => 
    let y : β  :=  f key
    match map.find? <| y with
    | some v =>
      map.insert y (min v val)
    | none => 
      map.insert y val
    ) FinDist.empty

def mapM{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (dist: FinDist α)(f: α → TermElabM β ) : TermElabM <| FinDist β  := 
  dist.toArray.foldlM (fun map (key, val) => do
    let y : β  ←  f key
    match map.find? <| y with
    | some v =>
      map.insert y (min v val)
    | none => 
      map.insert y val
    ) FinDist.empty

def weightCount{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) : HashMap Nat Nat := 
      m.toArray.foldl (fun w (key, val) =>
        match w.find? val with
        | some v =>
          w.insert val (v + 1)
        | none => 
          w.insert val 1
      ) HashMap.empty

def cumulWeightCount{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (maxWeight : Nat) : HashMap Nat Nat := Id.run do
      let base := weightCount m
      let mut w := HashMap.empty
      for (key, val) in base.toArray do
        for j in [key: (maxWeight + 1)] do
          match w.find? j with
          | some v =>
            w := w.insert j (v + val)
          | none => 
            w := w.insert j val
      return w

def filter{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (p: α → Bool) : FinDist α := 
  m.toArray.foldl (fun w (key, val) => 
    if p key then
      w.insert key val
    else w
  ) FinDist.empty

def filterM{α : Type}[Hashable α][BEq α]
    (m: FinDist α ) (p: α  → TermElabM Bool) : TermElabM <| FinDist α := do
  m.toArray.foldlM (fun w (key, val) => do 
    if ←  p key then
      w.insert key val
    else w
  ) FinDist.empty

def bound{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (maxWeight card: Nat)  : FinDist α := Id.run do
  let mut w := FinDist.empty
  let cumul := cumulWeightCount m
  let top := ((cumul maxWeight).toList.map (fun (k, v) => v)).maximum?.getD 1 
  for (key, val) in m.toArray do
    if val ≤ maxWeight && ((cumul maxWeight).findD val top ≤ card) then
      w := w.insert key val
  return w

def zeroLevel{α : Type}[Hashable α][BEq α] 
    (arr: Array α) : FinDist α := Id.run do
  arr.foldl (fun w x => w.insert x 0) FinDist.empty

def update{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (x: α) (d: Nat) : FinDist α := 
  match m.find? x with
  | some v => if d < v then m.insert x d else m
  | none => m.insert x d

def fromList{α : Type}[Hashable α][BEq α] (l : List (α  × Nat)) : FinDist α :=
  l.foldl (fun m (a, n) => m.update a n) HashMap.empty

def keys{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) := m.toList.map (fun (k, v) => k)

def findM?{α : Type}[Hashable α][BEq α] 
    (m: FinDist α)(p: α → TermElabM Bool) : TermElabM (Option (α × Nat)) := 
      findInList m.toList p 
    where
      findInList : List (α  × Nat) → (α → TermElabM Bool) → TermElabM (Option (α × Nat)) := 
        fun l p => do
          let mut res : Option (α × Nat) := none
          for (a, n) in l do
            if (← p a) && (res.map (fun (_, m) => n < m)).getD true then
              res := some (a, n)
          return res

end FinDist

def FinDist.exists{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (elem: α)(weight: Nat) : Bool :=
    match m.find? elem with
    | some v => v ≤ weight
    | none => false

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

  def addProof(m: ExprDist)(pf prop : Expr)(w: Nat) : ExprDist :=
    ⟨m.terms.insert pf w, m.proofs.insert prop (pf, w)⟩

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

end ExprDist

def ExprDist.existsM(dist: ExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
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

#check @Array.anyM