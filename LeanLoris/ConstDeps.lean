import Lean
import Lean.Meta
import Init.System
import Std
import LeanLoris.Utils
import LeanLoris.ExprPieces
import Lean.Data.Json.Basic
import Lean.Data.Json.Printer
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
open Lean Meta Std

/- 
Generating data of expressions in the definition and the types of global constants in the environment, with the goal of using for machine learning. System level definitions are excluded, based on the prefix of their names.

As this is experimental, various forms of data are generated.
-/

initialize exprRecCache : IO.Ref (HashMap Expr (Array Name)) ← IO.mkRef (HashMap.empty)

def getCached? (e : Expr) : IO (Option (Array Name)) := do
  let cache ← exprRecCache.get
  return cache.find? e

def cache (e: Expr) (offs : Array Name) : IO Unit := do
  let cache ← exprRecCache.get
  exprRecCache.set (cache.insert  e offs)
  return ()

/-- names of global constants -/
def constantNames  : MetaM (Array Name) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, _) => name 
  let names ← allNames.filterM (isWhiteListed)
  return names

/-- names with types of global constants -/
def constantNameTypes  : MetaM (Array (Name ×  Expr)) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, dfn) => (name, dfn.type) 
  let names ← allNames.filterM (fun (name, _) => isWhiteListed name)
  return names

/-- recursively find (whitelisted) names of constants in an expression; -/
partial def recExprNames: Expr → MetaM (Array Name) :=
  fun e =>
  do 
  match ← getCached? e with
  | some offs => return offs
  | none =>
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
            let ftype? ← inferType? f 
            let expl? := 
              ftype?.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := expl?.getD true
            let s ←  
              if !expl then recExprNames f else
                return (← recExprNames f) ++ (← recExprNames a)
            return s
      | Expr.lam _ _ b _ => 
          do
            return ← recExprNames b 
      | Expr.forallE _ _ b _ => do
          return  ← recExprNames b 
      | Expr.letE _ _ v b _ => 
            return (← recExprNames b) ++ (← recExprNames v)
      | _ => pure #[]
    cache e res
    return res

/-- names that are offspring of the constant with a given name -/
def offSpring? (name: Name) : MetaM (Option (Array Name)) := do
  let expr? ← nameExpr?  name
  match expr? with
  | some e => 
    return  some <| (← recExprNames e)
  | none => return none

/-- names that are descendant of the constant with a given name -/
partial def descendants (name: Name) : MetaM (Array Name) := do
  let off? ← offSpring? name
  match off? with 
  | some off => do
      let recDesc ← off.mapM (fun n => descendants n)
      return recDesc.foldl (fun acc n => acc.append n) #[name]
  | none => return #[name]

/-- names that are descendants of a given expression -/
def exprDescendants (expr: Expr) : MetaM (Array Name) := do
  let offs ← recExprNames expr
  let groups ← offs.mapM (fun n => descendants n)
  return groups.foldl (fun acc n => acc.append n) #[]

/-- 
Array of constants, names in their definition, and names in their type. 
-/
def offSpringTriple(excludePrefixes: List Name := [])
              : MetaM (Array (Name × (Array Name) × (Array Name) )) :=
  do
  let keys ←  constantNameTypes  
  IO.println s!"Tokens: {keys.size}"
  let goodKeys := keys.filter fun (name, _) =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name))
  IO.println s!"Tokens considered (excluding system code): {goodKeys.size}"
  let kv : Array (Name × (Array Name) × (Array Name)) ←  (goodKeys).mapM $ 
      fun (n, type) => 
          do 
          let l := (← offSpring? n).getD #[]
          let l := l.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          let tl ←  exprDescendants type
          let tl := tl.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          return (n, l, tl)
  return kv

/--
In core monad : array of constants, names in their definition, and names in their type. 
-/
def offSpringTripleCore: 
    CoreM (Array (Name × (Array Name) × (Array Name) )) := 
          (offSpringTriple [`Lean, `Std, `IO, 
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO]).run' 

/-- binomial pmf -/
def binom (n k: Nat)(p: Float) : Float := Id.run do
  let mut acc := ((1 - p)^ (n - k).toFloat)
  for i in [0:k] do 
      acc :=  acc * (n - i).toFloat * p / (k - i).toFloat
  return acc

/-- complement (wrt 1) of binomial cdf -/
def binomAbove (n k: Nat)(p: Float) : Float := Id.run do
  let mut acc := 0
  for j in [0: k] do
    acc :=  acc + (binom n j p)
  return 1.0 - acc 

def Array.countMap {α : Type}[BEq α][Hashable α] (arr: Array (α × Nat)) :
     HashMap α Nat :=
        HashMap.ofListWith (arr.toList) (Nat.add)

def Array.probMap {α : Type}[BEq α][Hashable α] (arr: Array (α × Nat)) :
     HashMap α Float :=
        let cnt := arr.countMap
        let total := arr.foldl (fun acc (a, n) => acc + n) 0
        if total = 0 then HashMap.empty else
          HashMap.ofList (
              cnt.toList.map $ fun (a, n) => (a, n.toFloat / total.toFloat))

def probOverlap {α : Type}[BEq α][Hashable α]
      (d d' : HashMap α Float) : Float :=
      let pq : Array Float := 
        d.toArray.filterMap (fun (a, p) => 
            (d'.find? a).map (fun x => min x p))
      pq.foldl (fun acc x => acc + x) 0.0 

/-- various frequencies of names in definitions and types -/
structure FrequencyData where
  size : Nat
  termFreqs: HashMap Name Nat
  typeFreqs: HashMap Name Nat
  typeTermFreqs: HashMap (Name × Name) Nat
  typeTermMap : HashMap Name (HashMap Name Nat)
  allObjects : HashSet Name
  triples: Array (Name × (Array Name) × (Array Name))

namespace FrequencyData

def asJsonM(fd: FrequencyData) : MetaM Json := do
  let namesJs := toJson fd.allObjects.toArray
  let proofs ← fd.allObjects.toArray.filterM (
      fun n => do isProof (← mkConstWithFreshMVarLevels n))
  let proofsJs :=  toJson <| proofs    
  let termsJs := toJson <| 
      fd.termFreqs.toArray.map (fun (n, c) => 
        Json.mkObj [("name", toJson n),("count", toJson c)])
  let typesJs := toJson <|
    fd.typeFreqs.toArray.map (fun (n, c) => 
        Json.mkObj [("name", toJson n),("count", toJson c)])
  let typeTermJs := toJson <| 
        fd.typeTermFreqs.toArray.map (
          fun ((term, type), count) =>
            Json.mkObj [("term", toJson term), ("type", toJson type), ("count", toJson count)])
        
  let typeTermMapJs := 
    toJson <| (fd.typeTermMap.toArray).map (fun (n, m) => 
       Json.mkObj [("type", toJson n), 
          ("terms", cntJson m.toArray)])
  let sizeJs := toJson fd.size
  let triplesJs := fd.triples.map (fun (n, l, t) => 
      Json.mkObj [("name", toJson n), ("terms", toJson l), ("types", toJson t)])
  return Json.mkObj [
    ("names", namesJs), ("proofs", proofsJs), ("terms", termsJs), ("types", typesJs),
    ("type-terms", typeTermJs), ("type-term-map", typeTermMapJs),
    ("size", sizeJs), ("triples", toJson triplesJs)]
  where cntJson (arr : Array (Name × Nat)) : Json :=
        toJson <| arr.map (fun (n, c) => Json.mkObj [("name", toJson n), ("count", toJson c)])

def asJson(fd: FrequencyData) : CoreM Json :=
  let m := asJsonM fd
  m.run'

/-- from off-spring triple obtain frequency data; not counting multiple occurences -/
def get (triples: Array (Name × (Array Name) × (Array Name))) : IO FrequencyData := do
  let size := triples.size
  let mut termFreqs := HashMap.empty
  let mut typeFreqs := HashMap.empty
  let mut typeTermFreqs := HashMap.empty
  let mut typeTermMap := HashMap.empty
  let mut allObjects := HashSet.empty
  for (name, terms, types) in triples do
    allObjects := allObjects.insert name
    for x in terms.toList.eraseDups do
      termFreqs := termFreqs.insert x ((termFreqs.findD x 0) + 1)
      allObjects := allObjects.insert x
    for x in types.toList.eraseDups do
      typeFreqs := typeFreqs.insert x ((typeFreqs.findD x 0) + 1)
      allObjects := allObjects.insert x
    for y in types.toList.eraseDups do
      for x in terms.toList.eraseDups do      
        typeTermFreqs := typeTermFreqs.insert (y, x) ((typeTermFreqs.findD (y, x) 0) + 1)
        let trms := (typeTermMap.findD y HashMap.empty)
        let trms := trms.insert x (trms.findD x 0 + 1)
        typeTermMap := typeTermMap.insert y trms 
  pure ⟨size, termFreqs, typeFreqs, typeTermFreqs, typeTermMap, allObjects, triples⟩

/-- from off-spring triple obtain frequency data; counting multiple occurences -/
def withMultiplicity(triples: Array (Name × (Array Name) × (Array Name))) : IO FrequencyData := do
  let size := triples.size
  let mut termFreqs := HashMap.empty
  let mut typeFreqs := HashMap.empty
  let mut typeTermFreqs := HashMap.empty
  let mut typeTermMap := HashMap.empty
  let mut allObjects := HashSet.empty
  for (name, terms, types) in triples do
    allObjects := allObjects.insert name
    for x in terms do
      termFreqs := termFreqs.insert x ((termFreqs.findD x 0) + 1)
      allObjects := allObjects.insert x
    for x in types do
      typeFreqs := typeFreqs.insert x ((typeFreqs.findD x 0) + 1)
      allObjects := allObjects.insert x
    for y in types do
      for x in terms do      
        typeTermFreqs := typeTermFreqs.insert (y, x) ((typeTermFreqs.findD (y, x) 0) + 1)
        let trms := (typeTermMap.findD y HashMap.empty)
        let trms := trms.insert x (trms.findD x 0 + 1)
        typeTermMap := typeTermMap.insert y trms 
  pure ⟨size, termFreqs, typeFreqs, typeTermFreqs, typeTermMap, allObjects, triples⟩

/-- frequency of occurence of names in definitions -/
def termFreqData (data: FrequencyData) : IO (Array (Name × Nat)) := do
  let freqs := data.termFreqs.toArray
  let freqs := freqs.qsort (fun  (k, v) (k', v') => v > v')
  return freqs

/-- frequency of occurence of names in types of definitions -/
def typeFreqData (data: FrequencyData) : IO (Array (Name × Nat)) := do
  let freqs := data.typeFreqs.toArray
  let freqs := freqs.qsort (fun  (k, v) (k', v') => v > v')
  return freqs
/--
data for predicting the likelihood of a name in a definition given types in the definition; in the form:
 `(type, term, p-value, conditional probability of term, probability of term) `
-/
def termPickData (data: FrequencyData) : (Array (Name × Name × Float × Float × Float)) :=  
  let baseTasks :=  data.typeTermFreqs.toArray.map $ fun ((type, term), k) =>
    Task.spawn fun _ =>
      let n := data.typeFreqs.find! type
      let p := (data.termFreqs.find! term).toFloat / data.size.toFloat
      (term, type, binomAbove n k p, k.toFloat / n.toFloat, p)
  let base := baseTasks.map $ fun t => t.get
  base.qsort (fun (_, _, x, _, _) (_, _, y, _, _) => x < y)

/-- 
array of names, frequencies of their occurence in types of definitions and the frequency of occurence of names in definitions where the given type occurs.
-/
def typeTermArray (data: FrequencyData) : Array (Name × Nat × (Array (Name × Nat))) := 
  let base := data.typeTermMap.toArray.map <| fun (type, terms) => 
      (type, data.typeFreqs.find! type, terms.toArray.qsort (fun (k, v) (k', v') => v > v'))
  base.qsort (fun (_, y, _) (_, y', _) => y > y')

/-- 
Crudely formatted: array of names, frequencies of their occurence in types of definitions and the frequency of occurence of names in definitions where the given type occurs.
-/
def typeTermView(data: FrequencyData) : String := 
  let arr : Array (Name × Nat × String)  := data.typeTermArray.map <| fun (type, freq, terms) => 
      (type, freq, (terms.toList.drop 1).foldl (fun acc (x, freq) => 
          let pair := s!"[\"{x}\", {freq}]"
          acc ++ "," ++ pair) s!"[\"{terms[0].1}\", {terms[0].2}]")
  let arr2 : Array String := arr.map $ fun (type, freq, terms) =>
        s!"[\"{type}\", {freq}, [{terms}]]"
  let multiline := (arr2.toList.drop 1).foldl (fun acc x => acc ++ ",\n" ++ x) s!"{arr2[0]}"
  s!"[{multiline}]"

end FrequencyData

/-- array names of definitions; frequency matrices of occurence of names in definitions and in types of definitions -/
def matrixData(triples: Array (Name × (Array Name) × (Array Name))) : 
      (Array Name) × (Array (Array Nat)) × (Array (Array Nat)) := Id.run do
        let mut allObjects : HashSet Name := HashSet.empty
        for (name, terms, types) in triples do
          allObjects := allObjects.insert name
          for x in terms do
            allObjects := allObjects.insert x
          for x in types do
            allObjects := allObjects.insert x
        let objects := allObjects.toArray
        let termsArray := triples.map $ fun (name, terms, types) =>
            countVec objects (count terms)
        let typesArr := triples.map $ fun (name, terms, types) =>
            countVec objects (count types)
        return ⟨objects, termsArray, typesArr⟩
        where 
          count (arr: Array Name) : HashMap Name Nat := Id.run do  
            let mut m := HashMap.empty
            for x in arr do
              m := m.insert x (m.findD x 0 + 1)
            return m
          countVec (objs: Array Name) (m: HashMap Name Nat) :=
            objs.map $ fun x => m.findD x 0

/-- Json data: array names of definitions; frequency matrices of occurence of names in definitions and in types of definitions -/
def matrixJson(triples: Array (Name × (Array Name) × (Array Name))) : Json :=
  let (objects, termsArray, typeTermsMatrix) := matrixData triples
  let namesJs := toJson objects
  let termsJs := toJson termsArray
  let typesJs := toJson typeTermsMatrix
  Json.mkObj [("names", namesJs), ("terms", termsJs), ("types", typesJs)]

/-- String of Json data: array names of definitions; frequency matrices of occurence of names in definitions and in types of definitions -/
def matrixView(triples: Array (Name × (Array Name) × (Array Name))) : String :=
  (matrixJson triples).pretty

