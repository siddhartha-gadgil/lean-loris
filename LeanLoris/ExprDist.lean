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
  termsArray : Array (Expr × Nat)
  proofsArray: Array (Expr × Expr × Nat)  
  termsTree : DiscrTree Nat
  proofsTree: DiscrTree (Expr × Nat)
namespace ExprDist
/--
The empty expression distribution.
-/
def empty : ExprDist := ⟨Array.empty, Array.empty, DiscrTree.empty, DiscrTree.empty⟩

def buildM(termsArray : Array (Expr × Nat))
          (proofsArray: Array (Expr × Expr × Nat)) : TermElabM ExprDist := do
          let mut termsTree := DiscrTree.empty
          let mut proofsTree := DiscrTree.empty
          for (x, d) in termsArray do
            termsTree ← termsTree.insert (← x.simplify) d
          for (prop, proof, d) in proofsArray do
            proofsTree ← proofsTree.insert (← prop.simplify) (proof, d)
          return ⟨termsArray, proofsArray, termsTree, proofsTree⟩

def termDegreeM?(d: ExprDist)(x: Expr) : TermElabM (Option Nat) := do
  let arr ← d.termsTree.getUnify (← x.simplify)
  if arr.isEmpty then return none
  else  return some <| arr.foldl (fun x y => Nat.min x y) arr[0]

def propDegreeM?(d: ExprDist)(prop: Expr) : TermElabM (Option Nat) := do
  let arr ← d.proofsTree.getUnify (← prop.simplify)
  let arr := arr.map (fun (_, d) => d)
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

/--
Adding a proof to an expression distribution. If the proposition is already present the proof is added only if the degree is lower than the existing one.
-/
def updateProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  let indexOpt := if !(← m.existsPropM prop d)  then none 
          else ← (m.proofsArray.findIdxM? <| fun (l, _, deg) =>  isDefEq l prop)
  match indexOpt  with
      | some j => 
          let (l, p, deg) := m.proofsArray.get! j
          if deg ≤ d then return m 
          else
            let newProofTree ← m.proofsTree.insert (← prop.simplify) (x, d)
            return ⟨m.termsArray, m.proofsArray.set! j (prop, x, d), 
                    m.termsTree, newProofTree⟩
      | none => 
          let newProofTree ← m.proofsTree.insert (← prop.simplify) (x, d)
          return ⟨m.termsArray, m.proofsArray.push (prop, x, d), 
                    m.termsTree, newProofTree⟩

/--
Adding a term to an expression distribution. If the term is already present the degree is added only if the degree is lower than the existing one.
-/
def updateTermM(m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    let indexOpt := if !(← m.existsM x d)  then none 
          else ← (m.termsArray.findIdxM? <| fun (t, deg) => isDefEq t x)
    match indexOpt with
      | some j =>
        let (t, deg) := m.termsArray.get! j 
        if deg ≤ d then return m
        else
          let newTermsTree ← m.termsTree.insert (← x.simplify) d 
          return ⟨m.termsArray.set! j (x, d), m.proofsArray, 
                    newTermsTree, m.proofsTree⟩
      | none => 
          let newTermsTree ← m.termsTree.insert (← x.simplify) d 
          return ⟨m.termsArray.push (x, d), m.proofsArray, 
                    newTermsTree, m.proofsTree⟩

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
  let newTermsTree ← m.termsTree.insert (← x.simplify) d 
  return ⟨m.termsArray.push (x, d), m.proofsArray, newTermsTree, m.proofsTree⟩

/--
Add a proof with no checks; to be used only if it is known that the proposition is not already present or has higher degree.
-/
def pushProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  let newProofTree ← m.proofsTree.insert (← prop.simplify) (x, d)
  return ⟨m.termsArray, m.proofsArray.push (prop, x, d), m.termsTree, newProofTree⟩

/--
Adds a proof if appropriate, and returns `some dist` if the distribution has been modified.
-/
def updatedProofM?(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM (Option ExprDist) := do
  let indexOpt := if !(← m.existsPropM prop d)  then none 
          else ← (m.proofsArray.findIdxM? <| fun (l, _, deg) =>  isDefEq l prop)
  match indexOpt  with
      | some j => 
          let (l, p, deg) := m.proofsArray.get! j
          if deg ≤ d then return none
          else let newProofTree ← m.proofsTree.insert (← prop.simplify) (x, d)
               return some  ⟨m.termsArray, m.proofsArray.push (prop, x, d), m.termsTree, newProofTree⟩
      | none => 
        let newProofTree ← m.proofsTree.insert (← prop.simplify) (x, d)
        return some  ⟨m.termsArray, m.proofsArray.push (prop, x, d), m.termsTree, newProofTree⟩

/--
Adds a term if appropriate, and returns `some dist` if the distribution has been modified.
-/
def updatedTermM?(m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    let indexOpt := if !(← m.existsM x d)  then none 
          else ← (m.termsArray.findIdxM? <| fun (t, deg) => isDefEq t x)
    match indexOpt with
      | some j =>
        let (t, deg) := m.termsArray.get! j 
        if deg ≤ j then return none
        else 
          let newTermsTree ← m.termsTree.insert (← x.simplify) d 
          return some ⟨m.termsArray.set! j (x, d), m.proofsArray, 
                    newTermsTree, m.proofsTree⟩
      | none => 
          let newTermsTree ← m.termsTree.insert (← x.simplify) d 
          return some ⟨m.termsArray.push (x, d), m.proofsArray, 
                    newTermsTree, m.proofsTree⟩
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
Groups an array of terms by the expression hash.
-/
def groupTermsByHash(terms : Array (Expr × Nat)) : 
      TermElabM (HashMap (UInt64) (Array (Expr × Nat))) := do
      terms.foldlM (fun m (e, deg) => 
        do
          let key ← exprHash e
          return m.insert key ((m.findD key #[]).push (e, deg))
          ) HashMap.empty

/--
Groups an array of proof triples by the expression hash of the proposition.
-/
def groupProofsByHash(proofs : Array (Expr × Expr × Nat)) : 
      TermElabM (HashMap (UInt64) (Array (Expr × Expr × Nat))) := do
      proofs.foldlM (fun m (l, pf, deg) => 
        do
          let key ← exprHash l
          return m.insert key ((m.findD key #[]).push (l, pf, deg))
          ) HashMap.empty

/--
Groups terms and proofs in a distribution by the appropriate hash.
-/
def groupDistByHash(arr: Array (Expr × Nat)) : TermElabM (HashMap (UInt64) ExprDist) := do
  arr.foldlM (fun m (e, deg) => do       
      if ← isProof e then
        let l ← inferType e
        let key ← exprHash l
        return m.insert key (← (m.findD key ExprDist.empty).pushProofM l e deg)
        else 
        let key ← exprHash e
        return m.insert key (← (m.findD key ExprDist.empty).pushTermM e deg)
      ) HashMap.empty

/--
Given grouped distributions by hash merge to a single one; it is assumed that the distributions are disjoint.
-/
def flattenDists(m: HashMap (UInt64) ExprDist) : TermElabM ExprDist := do
  let termArray := (m.toArray.map (fun (_, d) => d.termsArray)).foldl (fun a b => a.append b) Array.empty
  let pfArray := (m.toArray.map (fun (_, d) => d.proofsArray)).foldl (fun a b => a.append b) Array.empty
  buildM termArray pfArray

/--
Merge distributions by first grouping by hash.
-/
def mergeGroupedM(fst snd: ExprDist) : TermElabM ExprDist := do
    let ⟨fstTerms, fstProofs, _, _⟩ := fst
    let mut gpFstTerms ←  groupTermsByHash fstTerms
    let mut gpFstPfs ←  groupProofsByHash fstProofs
    let mut ⟨sndTerms, sndProofs, _, _⟩ := ExprDist.empty
    for (prop, x, d) in snd.proofsArray do
      let key ← exprHash prop
      match ← ((gpFstPfs.findD key #[]).findIdxM? <| fun (l, _, deg) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, deg) := (gpFstPfs.findD key #[]).get! j
          if deg ≤ d then pure ()
          else 
           gpFstPfs := gpFstPfs.insert key <| (gpFstPfs.findD key #[]).eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArray do
      let key ← exprHash x
      match ← ((gpFstTerms.findD key #[]).findIdxM? <| fun (t, deg) =>  isDefEq t x)  with
      | some j => 
          let (t, deg) := (gpFstTerms.findD key #[]).get! j
          if deg ≤ d then pure ()
          else 
           gpFstTerms := gpFstTerms.insert key <| (gpFstTerms.findD key #[]).eraseIdx j 
           sndTerms := sndTerms.push (x, d)
      | none => 
          sndTerms := sndTerms.push (x, d)
    let mut gpdDists : HashMap (UInt64) ExprDist := HashMap.empty
    for (key, termarr) in gpFstTerms.toArray do
      for (x, deg) in termarr do
        gpdDists :=  
          gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).pushTermM x deg)
    for (key, pfarr) in gpFstPfs.toArray do
      for (l, pf, deg) in pfarr do
        gpdDists :=  
          gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).pushProofM l pf deg)
    let fstDist ←  flattenDists gpdDists
    let res ← buildM (fstDist.termsArray ++ sndTerms) (fstDist.proofsArray ++ sndProofs)
    return res

/--
Compute the set difference of two distributions using hashes.
-/
def diffM(fst snd: ExprDist) : TermElabM ExprDist := do
    let ⟨sndTerms, sndProofs, _, _⟩ := snd
    let gpTerms ←  groupTermsByHash sndTerms
    let gpPfs ←  groupProofsByHash sndProofs
    let filteredTerms ←  fst.termsArray.filterM (fun (x, deg) => do
           let key ←  exprHash x
           let found ← 
              (gpTerms.findD key #[]).anyM (fun (y, deg') => (isDefEq x y) <&&> (return deg' ≤ deg))
           return !found)
    let filteredProofs ←  fst.proofsArray.filterM (fun (x, _, deg) => do
          let key ←  exprHash x
          let found ← (gpPfs.findD key #[]).anyM (fun (y, _, deg') => (isDefEq x y) <&&> (return deg' ≤ deg))
          return !found)
    buildM filteredTerms filteredProofs

/--
Merge without using hashes; not used currently but as the hashing is hacky this is not deleted.
-/
def mergeSimpleM(fst snd: ExprDist) : TermElabM ExprDist := do
    let mut ⟨fstTerms, fstProofs, _, _⟩ := fst
    let mut ⟨sndTerms, sndProofs, _, _⟩ := ExprDist.empty
    for (prop, x, d) in snd.proofsArray do
      let key ← exprHash prop
      match ← (fstProofs.findIdxM? <| fun (l, _, deg) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, deg) := fstProofs.get! j
          if deg ≤ d then pure ()
          else 
           fstProofs := fstProofs.eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArray do
      let key ← exprHash x
      match ← (fstTerms.findIdxM? <| fun (t, deg) =>  isDefEq t x)  with
      | some j => 
          let (t, deg) := fstTerms.get! j
          if deg ≤ d then pure ()
          else 
           fstTerms := fstTerms.eraseIdx j 
           sndTerms := sndTerms.push (x, d)
      | none => 
          sndTerms := sndTerms.push (x, d)
    let res ←  buildM (fstTerms ++ sndTerms) (fstProofs ++ sndProofs)
    return res

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeGroupedM⟩

/--
Form a distribution from an array of terms with degrees, where each term may or may not be a proof.
-/
def fromArrayM(arr: Array (Expr× Nat)): TermElabM ExprDist := do 
  let mut (terms, pfs) : (Array (Expr × Nat)) × (Array (Expr × Expr × Nat)) := 
    (#[], #[])
  for (e, n) in arr do
    if !(← isProof e) then
      terms := terms.push (e, n)
    else
      let l ← inferType e
      pfs := pfs.push (l, e, n)
  let gpTerms ←  groupTermsByHash terms
  let gpPfs ←  groupProofsByHash pfs
  let mut gpdDists : HashMap (UInt64) ExprDist := HashMap.empty
  for (key, termarr) in gpTerms.toArray do
    for (x, deg) in termarr do
      gpdDists :=  
        gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateTermM x deg)
  for (key, pfarr) in gpPfs.toArray do
    for (l, pf, deg) in pfarr do
      gpdDists :=  
        gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateProofM l pf deg)
  flattenDists gpdDists

/--
Form a distribution from an initial distribution and an array of terms with degrees, where each term may or may not be a proof.
-/
def mergeArrayM(fst: ExprDist)(arr: Array (Expr× Nat)): TermElabM ExprDist := do 
  let mut (terms, pfs) : (Array (Expr × Nat)) × (Array (Expr × Expr × Nat)) := 
    (#[], #[])
  for (e, n) in arr do
    if !(← isProof e) then
      terms := terms.push (e, n)
    else
      let l ← inferType e
      pfs := pfs.push (l, e, n)
  let gpTerms ←  groupTermsByHash terms
  let gpPfs ←  groupProofsByHash pfs
  let ⟨fstTerms, fstProofs, _, _⟩ := fst
    let mut gpFstTerms ←  groupTermsByHash fstTerms
    let mut gpFstPfs ←  groupProofsByHash fstProofs
  let mut gpdDists : HashMap (UInt64) ExprDist := HashMap.empty
  for (key, termarr) in gpFstTerms.toArray do
    let d ← buildM termarr #[]
    gpdDists := gpdDists.insert key d
  for (key, pfsArr) in gpFstPfs.toArray do
    let d ← buildM (
        (gpdDists.findD key ExprDist.empty).termsArray) pfsArr
    gpdDists := gpdDists.insert key d
  for (key, termarr) in gpTerms.toArray do
    for (x, deg) in termarr do
      gpdDists :=  
        gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateTermM x deg)
  for (key, pfarr) in gpPfs.toArray do
    for (l, pf, deg) in pfarr do
      gpdDists :=  
        gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateProofM l pf deg)
  flattenDists gpdDists

/--
Check if a term is present in a distribution, and with degree at most the specified degree.
-/
def existsOldM(dist: ExprDist)(elem: Expr)(degree: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      dist.proofsArray.anyM <| fun (l, _, deg) => 
              do pure (decide <| deg ≤ degree) <&&> isDefEq l prop
    else 
      dist.termsArray.anyM <| fun (t, deg) => 
              do pure (decide <| deg ≤ degree) <&&> isDefEq t elem

/--
Check if a proposition is present in a distribution, and with degree at least the specified degree.
-/
def existsPropOldM(dist: ExprDist)(prop: Expr)(degree: Nat) : TermElabM Bool :=
    dist.proofsArray.anyM <| fun (l, _, deg) => 
              do 
              let res ←  pure (decide <| deg ≤ degree) <&&> isDefEq l prop
              -- if res then 
              --   if !((← exprHash l) == (← exprHash prop)) then 
              --   IO.println s!"{l} = {prop} but {← exprHash l} != {← exprHash prop}"
              return res

/--
Array of terms including proofs with degrees.
-/
def allTermsArray(dist: ExprDist) : Array (Expr × Nat) :=
  dist.termsArray ++ 
          (dist.proofsArray.map <| fun (_, t, deg) => (t, deg))

/--
Array of sorts with degrees
-/
def allSortsArray(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let types ←  dist.termsArray.filterM <| fun (e, deg) => do
          return (← inferType e).isSort
  let props := dist.proofsArray.map <| fun (l, _, deg) => (l, deg)
  return types ++ props

/--
Cutoff a distribution at a given degree with given bound on cardinality.
-/
def boundM(dist: ExprDist)(degBnd: Nat)(cb: Option Nat) : TermElabM ExprDist := Id.run do
  let mut cumCount : HashMap Nat Nat := HashMap.empty
  for (_, deg) in dist.termsArray do
      for j in [deg:degBnd + 1] do
        cumCount := cumCount.insert j (cumCount.findD j 0 + 1)
  for (_, _, deg) in dist.proofsArray do
      for j in [deg:degBnd + 1] do
        cumCount := cumCount.insert j (cumCount.findD j 0 + 1)
  buildM (dist.termsArray.filter fun (_, deg) => 
      deg ≤ degBnd && (leqOpt (cumCount.find! deg) cb)) (
    dist.proofsArray.filter fun (_, _, deg) => deg ≤ degBnd && 
          (leqOpt (cumCount.find! deg) cb))
  
/--
Array of types with degrees.
-/
def typesArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  dist.termsArray.filterM <| fun (e, deg) => do
   isType e

/--
Array of propositions present as terms with degrees.
-/
def propsArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  dist.termsArray.filterM <| fun (e, deg) => do
   isProp e

/--
Array of functions with degrees, including proofs that are functions.
-/
def funcs(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let termFuncs ←   dist.termsArray.filterM $ fun (e, _) => 
       do return Expr.isForall <| ← inferType e
    let pfFuncs ← dist.proofsArray.filterMapM <| fun (l, f, deg) =>
      do if (l.isForall) then return some (f, deg) else return none
  return termFuncs ++ pfFuncs

/--
Array of equalities with degrees.
-/
def eqls(dist: ExprDist) : TermElabM (Array (Expr × Nat))  := do
  dist.proofsArray.filterMapM  $ fun (l, e, deg) => 
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
  dist.proofsArray.filterMapM  $ fun (l, e, deg) => 
       if isForallOfEqlty l then return some (e, deg) else return none

/--
Returns a proof of the proposition with degree if present in the distribution.
-/
def getProofM?(dist: ExprDist)(prop: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  let opt ←  dist.proofsArray.findM? <| fun (l, p, deg) => isDefEq l prop
  return opt.map <| fun (_, p, deg) => (p, deg)

/--
Checks whether a proof is present.
-/
def hasProof(dist: ExprDist)(prop: Expr) : TermElabM Bool := do
  dist.proofsArray.anyM <| fun (l, _, _) => isDefEq l prop

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
  dist.termsArray.findM? <| fun (t, deg) => isDefEq t elem

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
  let termsArrayBase ← dist.allTermsArray.mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  fromArrayM termsArrayBase


end ExprDist

/--
Distribution of hashes (in the usual sense) of expressions. This is to rapidly avoid too much duplication of computations involving expressions.
-/
structure HashExprDist where
  termsMap : FinDist UInt64
  propsMap : FinDist UInt64

def ExprDist.hashDist(expr: ExprDist) : HashExprDist := 
  { termsMap := FinDist.fromArray (expr.termsArray.map <| fun (e, deg) => (hash e, deg)),
    propsMap := FinDist.fromArray (expr.proofsArray.map <| fun (l, e, deg) => (hash e, deg)) }

def HashExprDist.existsM(dist: HashExprDist)(elem: Expr)(degree: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      return dist.propsMap.exists (hash prop) degree
    else 
      return dist.termsMap.exists (hash elem) degree
