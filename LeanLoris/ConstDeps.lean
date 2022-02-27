import Lean
import Lean.Meta
import Init.System
import Std
import LeanLoris.Utils
import LeanLoris.ExprPieces
open Lean Meta Std

initialize exprRecCache : IO.Ref (HashMap Expr (Array Name)) ← IO.mkRef (HashMap.empty)

def getCached? (e : Expr) : IO (Option (Array Name)) := do
  let cache ← exprRecCache.get
  return cache.find? e

def cache (e: Expr) (offs : Array Name) : IO Unit := do
  let cache ← exprRecCache.get
  exprRecCache.set (cache.insert  e offs)
  return ()


def constantNames  : MetaM (Array Name) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, _) => name 
  let names ← allNames.filterM (isWhiteListed)
  return names

def constantNameTypes  : MetaM (Array (Name ×  Expr)) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, dfn) => (name, dfn.type) 
  let names ← allNames.filterM (fun (name, _) => isWhiteListed name)
  return names

def inferTypeOpt(e: Expr) : MetaM (Option Expr) := do
  try
    let type ← inferType e
    return some type
  catch _ => return none


partial def recExprNames: Expr → MetaM (Array Name) :=
  fun e =>
  do 
  match ← getCached? e with
  | some offs => return offs
  | none =>
    -- IO.println s!"recExprNames: ${e}"
    let res ← match e with
      | Expr.const name _ _  =>
        do
        if ← (isWhiteListed name) 
          then return #[name] 
          else
          if ← (isNotAux name)  then
            match ←  nameExpr?  name with
            | some e => recExprNames e
            | none => return #[]
          else pure #[]        
      | Expr.app f a _ => 
          do  
            -- let ftype ← inferTypeIO f env
            let ftypeOpt ← inferTypeOpt f 
            let explOpt := 
              ftypeOpt.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := explOpt.getD true
            let fdeps ← recExprNames f
            let adeps ← recExprNames a
            let s := 
              if !expl then fdeps else
                fdeps ++ adeps
            return s
      | Expr.lam _ _ b _ => 
          do
            return ← recExprNames b 
      | Expr.forallE _ _ b _ => do
          return  ← recExprNames b 
      | Expr.letE _ _ _ b _ => 
            return ← recExprNames b
      | _ => pure #[]
    cache e res
    -- IO.println s!"found result recExprNames: ${e}"
    return res


def offSpring? (name: Name) : MetaM (Option (Array Name)) := do
  -- IO.println "finding offspring"
  let expr ← nameExpr?  name
  -- IO.println "found expr opt"
  match expr with
  | some e => 
    -- IO.println s!"found expr {e}"
    return  some <| (← recExprNames e)
  | none => return none

partial def descendants (name: Name) : MetaM (Array Name) := do
  let offOpt ← offSpring? name
  match offOpt with 
  | some off => do
      let recDesc ← off.mapM (fun n => descendants n)
      return recDesc.foldl (fun acc n => acc.append n) #[name]
  | none => return #[name]

def exprDescendants (expr: Expr) : MetaM (Array Name) := do
  -- IO.println s!"exprDescendants: {expr}"
  let offs ← recExprNames expr
  let groups ← offs.mapM (fun n => descendants n)
  return groups.foldl (fun acc n => acc.append n) #[]

def offSpringTriple(excludePrefixes: List Name := [])
              : MetaM (Array (Name × (Array Name) × (Array Name) )) :=
  do
  let keys ←  constantNameTypes  
  IO.println s!"keys: {keys.size}"
  let goodKeys := keys.filter fun (name, _) =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name))
  IO.println s!"good-keys: {goodKeys.size}"
  let kv : Array (Name × (Array Name) × (Array Name)) ←  (goodKeys).mapM $ 
      fun (n, type) => 
          do 
          -- IO.println $ "descendants of " ++ n ++ ": " 
          let l := (← offSpring? n).getD #[]
          let l := l.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          -- IO.println $ "found descendants of " ++ n ++ ": "
          let tl ←  exprDescendants type
          -- IO.println $ "found type descendants of " ++ n ++ ": "
          let tl := tl.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          return (n, l, tl)
  return kv

def offSpringTripleCore: 
    CoreM (Array (Name × (Array Name) × (Array Name) )) := 
          (offSpringTriple [`Lean, `Std, `IO, 
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO]).run' 

def binom (n k: Nat)(p: Float) : Float := Id.run do
  let mut acc := ((1 - p)^ (n - k).toFloat)
  for i in [0:k] do 
      acc :=  acc * (n - i).toFloat * p / (k - i).toFloat
  return acc

def binomAbove (n k: Nat)(p: Float) : Float := Id.run do
  let mut acc := 0
  for j in [k: n+ 1] do
    acc :=  acc + (binom n j p)
  return acc 


structure FrequencyData where
  size : Nat
  termFreqs: HashMap Name Nat
  typeFreqs: HashMap Name Nat
  typeTermFreqs: HashMap (Name × Name) Nat

namespace FrequencyData
def get (triples: Array (Name × (Array Name) × (Array Name))) : IO FrequencyData := do
  let size := triples.size
  let mut termFreqs := HashMap.empty
  let mut typeFreqs := HashMap.empty
  let mut typeTermFreqs := HashMap.empty
  for (_, terms, types) in triples do
    for x in terms.toList.eraseDups do
      termFreqs := termFreqs.insert x ((termFreqs.findD x 0) + 1)
    for x in types.toList.eraseDups do
      typeFreqs := typeFreqs.insert x ((typeFreqs.findD x 0) + 1)
    for y in types.toList.eraseDups do
      for x in terms.toList.eraseDups do      
        typeTermFreqs := typeTermFreqs.insert (y, x) ((typeTermFreqs.findD (y, x) 0) + 1)  
  pure ⟨size, termFreqs, typeFreqs, typeTermFreqs⟩

def termFreqData (data: FrequencyData) : IO (Array (Name × Nat)) := do
  let freqs := data.termFreqs.toArray
  let freqs := freqs.qsort (fun  (k, v) (k', v') => v > v')
  return freqs

def typeFreqData (data: FrequencyData) : IO (Array (Name × Nat)) := do
  let freqs := data.typeFreqs.toArray
  let freqs := freqs.qsort (fun  (k, v) (k', v') => v > v')
  return freqs

-- (type, term, p-value, conditional probability of term, probability of term) 
def termPickData (data: FrequencyData) : (Array (Name × Name × Float × Float × Float)) :=  
  let base :=  (data.typeTermFreqs.toList.take 1000).toArray.map $ fun ((type, term), k) =>
      let n := data.typeFreqs.find! type
      let p := (data.termFreqs.find! term).toFloat / data.size.toFloat
      (term, type, binomAbove n k p, k.toFloat / n.toFloat, p)
  base.qsort (fun (_, _, x, _, _) (_, _, y, _, _) => x < y)

end FrequencyData

#eval binomAbove 10 9 0.5