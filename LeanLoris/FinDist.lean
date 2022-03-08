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

/-- 
  Hashmaps for distributions;  with basic map, filter methods
  including Mondaic forms. For expressions we use `ExprDist` instead
  as we want Definitional equality, not Boolean equality.
-/
abbrev FinDist (α : Type)[Hashable α][BEq α] := HashMap α Nat 

/--
Distribution on names
-/
abbrev NameDist := FinDist Name

namespace FinDist

def empty{α : Type} [Hashable α][BEq α] : FinDist α := HashMap.empty

/--
Merge finite distributions, with the lowest value for a key
-/
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

/--
map finite distributions, taking lowest value when images of keys are equal.
-/
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

/--
monadic map finite distributions, taking lowest value when images of keys are equal.
-/
def mapM{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (dist: FinDist α)(f: α → TermElabM β ) : TermElabM <| FinDist β  := 
  dist.toArray.foldlM (fun map (key, val) => do
    let y : β  ←  f key
    match map.find? <| y with
    | some v =>
      return map.insert y (min v val)
    | none => 
      return map.insert y val
    ) FinDist.empty

/--
number of keys with given value
-/
def weightCount{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) : HashMap Nat Nat := 
      m.toArray.foldl (fun w (key, val) =>
        match w.find? val with
        | some v =>
          w.insert val (v + 1)
        | none => 
          w.insert val 1
      ) HashMap.empty

/--
number of keys with value greater than or equal to given value, up to the maximum value
-/
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

/--
filter the distribution.
-/
def filter{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (p: α → Bool) : FinDist α := 
  m.toArray.foldl (fun w (key, val) => 
    if p key then
      w.insert key val
    else w
  ) FinDist.empty

/--
monadic filter for the distribution.
-/
def filterM{α : Type}[Hashable α][BEq α]
    (m: FinDist α ) (p: α  → TermElabM Bool) : TermElabM <| FinDist α := do
  m.toArray.foldlM (fun w (key, val) => do 
    if ← p key then
      return w.insert key val
    else return w
  ) FinDist.empty

/--
cutoff the distribution given maximum weight and cardinality
-/
def bound{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (maxWeight card: Nat)  : FinDist α := Id.run do
  let mut w := FinDist.empty
  let cumul := cumulWeightCount m
  let top := ((cumul maxWeight).toList.map (fun (k, v) => v)).maximum?.getD 1 
  for (key, val) in m.toArray do
    if val ≤ maxWeight && ((cumul maxWeight).findD val top ≤ card) then
      w := w.insert key val
  return w

/--
return distribution with all weights zero 
-/
def zeroLevel{α : Type}[Hashable α][BEq α] 
    (arr: Array α) : FinDist α := Id.run do
  arr.foldl (fun w x => w.insert x 0) FinDist.empty

/--
update the distribution, adding a key only if it is not already present
or has a lower weight.
-/
def update{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (x: α) (d: Nat) : FinDist α := 
  match m.find? x with
  | some v => if d < v then m.insert x d else m
  | none => m.insert x d

/--
distribution from list of weighted elements.
-/
def fromList{α : Type}[Hashable α][BEq α] (l : List (α  × Nat)) : FinDist α :=
  l.foldl (fun m (a, n) => m.update a n) HashMap.empty

/--
distribution from array of weighted elements.
-/
def fromArray{α : Type}[Hashable α][BEq α] (arr: Array (α × Nat)) : FinDist α :=
  arr.foldl (fun m (x, w) => m.update x w) HashMap.empty

/--
the keys
-/
def keys{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) := m.toList.map (fun (k, v) => k)

/--
(monadic) find optional weight of given element.
-/
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

/--
check if element exists with weight at most the bound.
-/
def FinDist.exists{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (elem: α)(weight: Nat) : Bool :=
    match m.find? elem with
    | some v => v ≤ weight
    | none => false

/--
given an array of elements with weights, return a map of the number of
elements with weight at least a given number, up to the maximum weight.
-/
def weightAbove{α : Type}(wtd : Array (α × Nat))(maxWeight: Nat): 
    HashMap Nat Nat := Id.run do
      let mut w := HashMap.empty
      for (_, n) in wtd do
        for j in [n: (maxWeight + 1)] do
          match w.find? j with
          | some v =>
            w := w.insert j (v + 1)
          | none => 
            w := w.insert j 1
      return w

/--
return map of number of elements with a given weight in an array of pairs.
-/
def arrWeightCount{α : Type}[Hashable α][BEq α] 
    (m: Array (α× Nat)) : HashMap Nat Nat := 
      m.foldl (fun w (key, val) =>
        match w.find? val with
        | some v =>
          w.insert val (v + 1)
        | none => 
          w.insert val 1
      ) HashMap.empty