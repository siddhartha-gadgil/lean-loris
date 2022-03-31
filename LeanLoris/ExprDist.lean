import LeanLoris.FinDist
import LeanLoris.ExprPieces
import LeanLoris.Utils
import Lean.Meta
import Lean.Elab
import Std
import Lean
open Lean
open PrettyPrinter
open Meta
open Elab
open Lean.Elab.Term
open Std
open Std.HashMap
open Nat

/--
Expressions with degrees, with degrees to be viewed as (unscaled) entropies, i.e., a lower degree means a higher probability of being chosen. There are two fields, with terms representing expressions that are not proofs.

There should be at most one `(term, degree)` pair for each term up to definitional equality. This is assumed at each stage and all operations must ensure this property holds. 

Proofs are stored as triples `(propn, proof, degree)`. There is at most one such triple for each proposition up to definitional equality. This is assumed at each stage and all operations must ensure this property holds.

When new terms or proofs are added or distributions are merged, the term or proposition with the lower degree is included in the new distribution.

All the operations use `exprHash`, which is a hacky hash associated to expressions that seems to work well.
-/
structure ExprDist where
  termsTree : DiscrTree (Expr × Nat)
  proofsTree: DiscrTree (Expr × Expr × Nat)
  keys : Array Expr
namespace ExprDist
/--
The empty expression distribution.
-/
def empty : ExprDist := ⟨DiscrTree.empty, DiscrTree.empty, #[]⟩

def addKeyM (d: ExprDist)(key: Expr) : TermElabM ExprDist := do 
  if !(← d.termsTree.getMatch key).isEmpty || !(← d.termsTree.getMatch key).isEmpty 
  then return d
  else return ⟨d.termsTree, d.proofsTree, d.keys.push key⟩

def buildM(termsArray : Array (Expr × Nat))
          (proofsArray: Array (Expr × Expr × Nat)) : TermElabM ExprDist := do
          let mut termsTree : DiscrTree (Expr × Nat) := DiscrTree.empty
          let mut proofsTree :  DiscrTree (Expr × Expr × Nat) := DiscrTree.empty
          let mut keys := #[]
          for (x, d) in termsArray do
            let key ← x.simplify
            termsTree ← termsTree.insert key (x,d)
            if (← termsTree.getMatch key).isEmpty && (← termsTree.getMatch key).isEmpty
            then keys := keys.push key
          for (prop, proof, d) in proofsArray do
            let key ← prop.simplify
            proofsTree ← proofsTree.insert key (prop, proof, d)
            if (← termsTree.getMatch key).isEmpty && (← termsTree.getMatch key).isEmpty
            then keys := keys.push key
          return ⟨termsTree, proofsTree, keys⟩

def termDegreeM?(d: ExprDist)(x: Expr) : TermElabM (Option Nat) := do
  let arr ← d.termsTree.getMatch (← x.simplify)
  let arr ← arr.filterM <| fun (y, _) => isDefEq x y
  if arr.isEmpty then return none
  else  return some <| arr.foldl (fun x (_, y) => Nat.min x y) arr[0].2

def propDegreeM?(d: ExprDist)(prop: Expr) : TermElabM (Option Nat) := do
  let arr ← d.proofsTree.getMatch (← prop.simplify)
  let arr ← arr.filterM (fun ⟨p, _, _⟩ => isDefEq prop p)
  let arr := arr.map (fun (_, _, d) => d)
  if arr.isEmpty then return none
  else  return some <| arr.foldl (fun x y => Nat.min x y) arr[0]

def existsM(d: ExprDist)(x: Expr)(deg : Nat) : TermElabM Bool := do
  match ← termDegreeM? d x with
  | none => return false
  | some deg' => return deg' ≤ deg

def existsPropM(d: ExprDist)(prop: Expr)(deg : Nat) : TermElabM Bool := do
  match ← propDegreeM? d prop with
  | none => return false
  | some deg' => return deg' ≤ deg

def termsArrayM(d: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let mut arr := #[]
  for key in d.keys do
    for (x, deg) in ← d.termsTree.getMatch key do
      arr := arr.push (x, deg)
  return arr

def proofsArrayM(d: ExprDist) : TermElabM (Array (Expr × Expr × Nat)) := do
  let mut arr := #[]
  for key in d.keys do
    for (l, pf, deg) in ← d.proofsTree.getMatch key do
      arr := arr.push (l, pf, deg)
  return arr

/--
Adding a proof to an expression distribution. If the proposition is already present the proof is added only if the degree is lower than the existing one.
-/
def updateProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  if ← m.existsPropM prop d then return m
  else do
    let key ← prop.simplify
    let m ← m.addKeyM key
    return ⟨m.termsTree, ← m.proofsTree.insert key (prop, x, d), m.keys⟩

/--
Adding a term to an expression distribution. If the term is already present the degree is added only if the degree is lower than the existing one.
-/
def updateTermM(m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    if ← m.existsM x d then return m
    else do
      let key ← x.simplify
      let m ← m.addKeyM key
      return ⟨← m.termsTree.insert key (x, d), m.proofsTree, m.keys⟩


/--
Adding a term or proof to a distribution, checking that the term or proposition is not already present or has higher degree.
-/
def updateExprM
    (m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    if ← isProof x then
      let prop ← whnf (← inferType x)
      Term.synthesizeSyntheticMVarsNoPostponing
      updateProofM m prop x d
    else 
      updateTermM m x d

/--
Add a term with no checks; to be used only if it is known that the term is not already present or has higher degree.
-/
def pushTermM(m: ExprDist)(x: Expr)(d: Nat) : TermElabM ExprDist := do
  let key ← x.simplify
  let m ← m.addKeyM key
  let newTermsTree ← m.termsTree.insert (← x.simplify) (x, d) 
  return ⟨newTermsTree, m.proofsTree, m.keys⟩

/--
Add a proof with no checks; to be used only if it is known that the proposition is not already present or has higher degree.
-/
def pushProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  let key ← prop.simplify
  let m ← m.addKeyM key
  let newProofTree ← m.proofsTree.insert (← prop.simplify) (prop, x, d)
  return ⟨m.termsTree, newProofTree, m.keys⟩
/--
Adds a proof if appropriate, and returns `some dist` if the distribution has been modified.
-/
def updatedProofM?(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM (Option ExprDist) := do
  if ← m.existsPropM prop d then return none
  else do
    let key ← prop.simplify
    let m ← m.addKeyM key
    return some ⟨m.termsTree, ← m.proofsTree.insert key (prop, x, d), m.keys⟩

/--
Adds a term if appropriate, and returns `some dist` if the distribution has been modified.
-/
def updatedTermM?(m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    if ← m.existsM x d then return none
    else do
      let key ← x.simplify
      let m ← m.addKeyM key
      return some  ⟨← m.termsTree.insert key (x, d), m.proofsTree, m.keys⟩
/--
Adds a term or proof if appropriate, and returns `some dist` if the distribution has been modified.
-/
def updatedExprM?
    (m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    if ← isProof x then
      let prop ← whnf (← inferType x)
      Term.synthesizeSyntheticMVarsNoPostponing
      updatedProofM? m prop x d
    else 
      updatedTermM? m x d

/--
Compute the set difference of two distributions using hashes.
-/
def diffM(fst snd: ExprDist) : TermElabM ExprDist := do
    let mut dist := ExprDist.empty
    for key in fst.keys do
      for (x, deg) in (← fst.termsTree.getMatch key) do
        unless ← snd.existsM x deg do
          dist ← dist.updateTermM x deg
      for (prop, pf, deg) in (← fst.proofsTree.getMatch key) do
        unless ← snd.existsPropM prop deg do
          dist ← dist.updateProofM prop pf  deg
    return dist

/--
Merge without using hashes; not used currently but as the hashing is hacky this is not deleted.
-/
def mergeSimpleM(fst snd: ExprDist) : TermElabM ExprDist := do
    let mut dist := fst
    for key in snd.keys do
      for (x, deg) in (← snd.termsTree.getMatch key) do
        dist ← dist.updateTermM x deg
      for (prop, pf, deg) in (← snd.proofsTree.getMatch key) do
        dist ← dist.updateProofM prop pf deg
    return dist

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeSimpleM⟩

/--
Form a distribution from an array of terms with degrees, where each term may or may not be a proof.
-/
def fromArrayM(arr: Array (Expr× Nat)): TermElabM ExprDist := do 
  let mut dist := ExprDist.empty
  for (e, n) in arr do
    if !(← isProof e) then
      dist ← dist.updateTermM e n
    else
      let l ← inferType e
      dist ← dist.updateProofM l e n
  return dist

/--
Form a distribution from an initial distribution and an array of terms with degrees, where each term may or may not be a proof.
-/
def mergeArrayM(fst: ExprDist)(arr: Array (Expr× Nat)): TermElabM ExprDist := do
  let mut dist := fst
  for (e, n) in arr do
    if !(← isProof e) then
      dist ← dist.updateTermM e n
    else
      let l ← inferType e
      dist ← dist.updateProofM l e n
  return dist


/--
Array of terms including proofs with degrees.
-/
def allTermsArrayM(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let proofsArray ← dist.proofsArrayM
  return (← dist.termsArrayM) ++ 
          (proofsArray.map <| fun (_, t, deg) => (t, deg))

/--
Array of sorts with degrees
-/
def allSortsArray(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let types ←  (← dist.termsArrayM).filterM <| fun (e, deg) => do
          return (← inferType e).isSort
  let props := (← dist.proofsArrayM).map <| fun (l, _, deg) => (l, deg)
  return types ++ props

/--
Cutoff a distribution at a given degree with given bound on cardinality.
-/
def boundM(dist: ExprDist)(degBnd: Nat)(cb: Option Nat) : TermElabM ExprDist := do
  let mut cumCount : HashMap Nat Nat := HashMap.empty
  for (_, deg) in (← dist.termsArrayM) do
      for j in [deg:degBnd + 1] do
        cumCount := cumCount.insert j (cumCount.findD j 0 + 1)
  for (_, _, deg) in (← dist.proofsArrayM) do
      for j in [deg:degBnd + 1] do
        cumCount := cumCount.insert j (cumCount.findD j 0 + 1)
  buildM ((← dist.termsArrayM).filter fun (_, deg) => 
      deg ≤ degBnd && (leqOpt (cumCount.find! deg) cb)) (
    (← dist.proofsArrayM).filter fun (_, _, deg) => deg ≤ degBnd && 
          (leqOpt (cumCount.find! deg) cb))
  
/--
Array of types with degrees.
-/
def typesArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  (← dist.termsArrayM).filterM <| fun (e, deg) => do
   isType e

/--
Array of propositions present as terms with degrees.
-/
def propsArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  (← dist.termsArrayM).filterM <| fun (e, deg) => do
   isProp e

/--
Array of functions with degrees, including proofs that are functions.
-/
def funcs(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let termFuncs ←   (← dist.termsArrayM).filterM $ fun (e, _) => 
       do return Expr.isForall <| ← inferType e
  let pfFuncs ← (← dist.proofsArrayM).filterMapM <| fun (l, f, deg) =>
      do if (l.isForall) then return some (f, deg) else return none
  return termFuncs ++ pfFuncs

/--
Array of equalities with degrees.
-/
def eqls(dist: ExprDist) : TermElabM (Array (Expr × Nat))  := do
  (← dist.proofsArrayM).filterMapM  $ fun (l, e, deg) => 
       do if l.isEq then return some (e, deg) else return none

/--
Checks whether expression is a universally quantified equality.
-/
def isForallOfEqlty(l: Expr): Bool := 
  if l.isEq then true
  else 
    match l with
       | Expr.forallE _ _ b _  => isForallOfEqlty b
       | _ => false

/--
Array of uniformly quantified equalities with degrees.
-/
def forallOfEquality(dist: ExprDist) : TermElabM (Array (Expr × Nat))  := do
  (← dist.proofsArrayM).filterMapM  $ fun (l, e, deg) => 
       if isForallOfEqlty l then return some (e, deg) else return none

/--
Returns a proof of the proposition with degree if present in the distribution.
-/
def getProofM?(dist: ExprDist)(prop: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  let opt ←  (← dist.proofsArrayM).findM? <| fun (l, p, deg) => isDefEq l prop
  return opt.map <| fun (_, p, deg) => (p, deg)

/--
Checks whether a proof is present.
-/
def hasProof(dist: ExprDist)(prop: Expr) : TermElabM Bool := do
  (← dist.proofsArrayM).anyM <| fun (l, _, _) => isDefEq l prop

/--
Array of propositions with degrees that are present as proofs and whose proofs are not present.
-/
def goalsArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  (← dist.propsArr).filterM <| fun (e, deg) => do
    return !(← dist.hasProof e)

/--
Returns a term with degree which is definitionally equal to the given term if present.
-/
def getTermM?(dist: ExprDist)(elem: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  (← dist.termsArrayM).findM? <| fun (t, deg) => isDefEq t elem

/--
Array of proofs with degrees that are in the distribution for given goals;
also returns terms that are equal to the goals if `showStatements` is `true`.
-/
def getGoalsM(dist: ExprDist)(goals : Array Expr)
  (showStatement: Bool := false) : 
  TermElabM (Array (Expr × Expr × Nat )) := 
  do
    goals.filterMapM <| fun g => do 
      let wpf ← dist.getProofM? g
      let dg ← dist.getTermM? g
      let res := if (showStatement) then wpf.orElse (fun _ => dg) else wpf
      return res.map (fun (x, deg) => (g, x, deg))

/--
Formatted proofs with degrees that are in the distribution for given goals;
also returns terms that are equal to the goals if `showStatements` is `true`.
-/
def viewGoalsM(dist: ExprDist)(goals : Array Expr)(showStatement: Bool := false) 
    : TermElabM String :=
  do
    let pfs ← dist.getGoalsM goals showStatement
    let view : Array String ←  pfs.mapM <| fun (g, pf, deg) => do
      return s!"Theorem: {← view g}\nProof: {← view pf}; degree: {deg}\n"
    let s := view.foldl (fun acc e => acc ++ "\n" ++ e) "## Proofs obtained:\n"
    return s

/--
Run from `TermElabM` monad to `CoreM` monad for strings.
-/
def coreView(l : TermElabM String) : CoreM  String := do
      let m := l.run'
      m.run'

/--
Find degree of term if present or return default.
-/
def findD(dist: ExprDist)(elem: Expr)(default: Nat) : TermElabM Nat := do
  return (← termDegreeM? dist elem).getD default
  -- match ← getTermM? dist elem with
  -- | some (t, deg) =>
  --   let deg' ← dist.termDegreeM? elem
  --   unless (deg' = some deg) do
  --     IO.println s!"Warning: term degree changed from {deg} to {deg'}"
  --   pure deg
  -- | none => pure default

def mapM(dist: ExprDist)(f: Expr → TermElabM Expr) : TermElabM ExprDist := do
  let termsArrayBase ← (← dist.allTermsArrayM).mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  fromArrayM termsArrayBase


end ExprDist


/--
-Distribution of hashes (in the usual sense) of expressions. This is to rapidly avoid too much duplication of computations involving expressions.
-/
structure HashExprDist where
  termsMap : FinDist UInt64
  propsMap : FinDist UInt64

def ExprDist.hashDist(expr: ExprDist) : TermElabM HashExprDist := do 
  return ⟨ FinDist.fromArray ((← expr.termsArrayM).map <| fun (e, deg) => (hash e, deg)),
    FinDist.fromArray ((← expr.proofsArrayM).map <| fun (l, e, deg) => (hash e, deg)) ⟩

def HashExprDist.existsM(dist: HashExprDist)(elem: Expr)(degree: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      return dist.propsMap.exists (hash prop) degree
    else 
      return dist.termsMap.exists (hash elem) degree

