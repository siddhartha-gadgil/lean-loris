import LeanLoris.FinDist
import LeanLoris.ExprPieces
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

-- proofs will not also be stored as terms
structure ExprDist where
  termsArr : Array (Expr × Nat)
  proofsArr: Array (Expr × Expr × Nat)  
namespace ExprDist

def empty : ExprDist := ⟨Array.empty, Array.empty⟩

def updateProofM(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM ExprDist := do
  match ← (m.proofsArr.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := m.proofsArr.get! j
          -- if !((← argList l) == (← argList prop)) then 
          --   IO.println s!"{l} = {prop} but {← argList l} != {← argList prop}"
          if w ≤ d then return m 
          else return ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updateTermM(m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => isDefEq t x) with
      | some j =>
        let (t, w) := m.termsArr.get! j 
        -- if !((← argList x) == (← argList t)) then 
        --     IO.println s!"{x} = {t} but {← argList x} != {← argList t}"
        if w ≤ j then return m
        else return ⟨m.termsArr.set! j (x, d), m.proofsArr⟩
      | none => 
          return ⟨m.termsArr.push (x, d), m.proofsArr⟩

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
  ⟨m.termsArr.push (x, d), m.proofsArr⟩

def pushProof(m: ExprDist)(prop x: Expr)(d: Nat) : ExprDist :=
  ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updatedProofM?(m: ExprDist)(prop x: Expr)(d: Nat) : TermElabM (Option ExprDist) := do
  match ← (m.proofsArr.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := m.proofsArr.get! j
          -- if !((← argList l) == (← argList prop)) then 
          --   IO.println s!"{l} = {prop} but {← argList l} != {← argList prop}"
          if w ≤ d then return none
          else return some ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return some ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updatedTermM?(m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => isDefEq t x) with
      | some j =>
        let (t, w) := m.termsArr.get! j 
        -- if !((← argList x) == (← argList t)) then 
        --     IO.println s!"{x} = {t} but {← argList x} != {← argList t}"
        if w ≤ j then return none
        else return some ⟨m.termsArr.set! j (x, d), m.proofsArr⟩
      | none => 
          return some ⟨m.termsArr.push (x, d), m.proofsArr⟩

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
  let termsArrBase ← dist.termsArr.mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  termsArrBase.foldlM (fun  dist (e, n) => 
    do dist.updateExprM e n) empty

def groupTermsByArgs(terms : Array (Expr × Nat)) : 
      TermElabM (HashMap (List Name) (Array (Expr × Nat))) := do
      terms.foldlM (fun m (e, w) => 
        do
          let key ← argList e
          m.insert key ((m.findD key #[]).push (e, w))
          ) HashMap.empty

def groupProofsByArgs(proofs : Array (Expr × Expr × Nat)) : 
      TermElabM (HashMap (List Name) (Array (Expr × Expr × Nat))) := do
      proofs.foldlM (fun m (l, pf, w) => 
        do
          let key ← argList l
          m.insert key ((m.findD key #[]).push (l, pf, w))
          ) HashMap.empty

def groupDistByArgs(arr: Array (Expr × Nat)) : TermElabM (HashMap (List Name) ExprDist) := do
  arr.foldlM (fun m (e, w) => do       
      if ← isProof e then
        let l ← inferType e
        let key ← argList l
        m.insert key ((m.findD key ExprDist.empty).pushProof l e w)
        else 
        let key ← argList e
        m.insert key ((m.findD key ExprDist.empty).pushTerm e w)
      ) HashMap.empty

def flattenDists(m: HashMap (List Name) ExprDist) : TermElabM ExprDist := do
  let termList := m.toList.bind (fun (_, d) => d.termsArr.toList)
  let pfList := m.toList.bind (fun (_, d) => d.proofsArr.toList)
  -- IO.println s!"termList = {termList.length}"
  -- IO.println s!"pfList = {pfList.length}"
  return ⟨termList.toArray, pfList.toArray⟩

def mergeGroupedM(fst snd: ExprDist) : TermElabM ExprDist := do
    -- logInfo m!"merging; time: {← IO.monoMsNow}; sizes: ({fst.termsArr.size}, {fst.proofsArr.size}) ({snd.termsArr.size}, {snd.proofsArr.size})"
    let mut dist := fst
    let ⟨fstTerms, fstProofs⟩ := fst
    let mut gpFstTerms ←  groupTermsByArgs fstTerms
    let mut gpFstPfs ←  groupProofsByArgs fstProofs
    let mut ⟨sndTerms, sndProofs⟩ := ExprDist.empty
    for (prop, x, d) in snd.proofsArr do
      let key ← argList prop
      match ← ((gpFstPfs.findD key #[]).findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := (gpFstPfs.findD key #[]).get! j
          -- if !((← argList l) == (← argList prop)) then 
          --   IO.println s!"{l} = {prop} but {← argList l} != {← argList prop}"
          if w ≤ d then ()
          else 
           gpFstPfs := gpFstPfs.insert key <| (gpFstPfs.findD key #[]).eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArr do
      let key ← argList x
      match ← ((gpFstTerms.findD key #[]).findIdxM? <| fun (t, w) =>  isDefEq t x)  with
      | some j => 
          let (t, w) := (gpFstTerms.findD key #[]).get! j
          -- if !((← argList x) == (← argList t)) then 
          --   IO.println s!"{x} = {t} but {← argList x} != {← argList t}"
          if w ≤ d then ()
          else 
           gpFstTerms := gpFstTerms.insert key <| (gpFstTerms.findD key #[]).eraseIdx j 
           sndTerms := sndTerms.push (x, d)
      | none => 
          sndTerms := sndTerms.push (x, d)
    let mut gpdDists : HashMap (List Name) ExprDist := HashMap.empty
    for (key, termarr) in gpFstTerms.toArray do
      for (x, w) in termarr do
        gpdDists :=  
          gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateTermM x w)
    for (key, pfarr) in gpFstPfs.toArray do
      for (l, pf, w) in pfarr do
        gpdDists :=  
          gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateProofM l pf w)
    let fstDist ←  flattenDists gpdDists
    let res := ⟨fstDist.termsArr ++ sndTerms, fstDist.proofsArr ++ sndProofs⟩
    -- logInfo m!"merged arrays obtained; time: {← IO.monoMsNow}; size: {fstTerms.size + sndTerms.size}; {fstProofs.size + sndProofs.size}"
    return res

def mergeM(fst snd: ExprDist) : TermElabM ExprDist := do
    -- logInfo m!"merging; time: {← IO.monoMsNow}; sizes: ({fst.termsArr.size}, {fst.proofsArr.size}) ({snd.termsArr.size}, {snd.proofsArr.size})"
    let mut dist := fst
    let mut ⟨fstTerms, fstProofs⟩ := fst
    let mut ⟨sndTerms, sndProofs⟩ := ExprDist.empty
    for (prop, x, d) in snd.proofsArr do
      let key ← argList prop
      match ← (fstProofs.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := fstProofs.get! j
          -- if !((← argList l) == (← argList prop)) then 
          --   IO.println s!"{l} = {prop} but {← argList l} != {← argList prop}"
          if w ≤ d then ()
          else 
           fstProofs := fstProofs.eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArr do
      let key ← argList x
      match ← (fstTerms.findIdxM? <| fun (t, w) =>  isDefEq t x)  with
      | some j => 
          let (t, w) := fstTerms.get! j
          -- if !((← argList x) == (← argList t)) then 
          --   IO.println s!"{x} = {t} but {← argList x} != {← argList t}"
          if w ≤ d then ()
          else 
           fstTerms := fstTerms.eraseIdx j 
           sndTerms := sndTerms.push (x, d)
      | none => 
          sndTerms := sndTerms.push (x, d)
    let res := ⟨fstTerms ++ sndTerms, fstProofs ++ sndProofs⟩
    -- logInfo m!"merged arrays obtained; time: {← IO.monoMsNow}; size: {fstTerms.size + sndTerms.size}; {fstProofs.size + sndProofs.size}"
    return res

instance : HAppend ExprDist ExprDist (TermElabM ExprDist) := 
  ⟨ExprDist.mergeGroupedM⟩

def fromTermsM(dist: FinDist Expr): TermElabM ExprDist := do
  dist.foldM  (fun m e n => m.updateExprM e n) ExprDist.empty

def fromArray(arr: Array (Expr× Nat)): TermElabM ExprDist := do 
  let mut (terms, pfs) : (Array (Expr × Nat)) × (Array (Expr × Expr × Nat)) := 
    (#[], #[])
  for (e, n) in arr do
    if !(← isProof e) then
      terms := terms.push (e, n)
    else
      let l ← inferType e
      pfs := pfs.push (l, e, n)
  -- IO.println s!"terms = {terms.size}; pfs = {pfs.size}"
  let gpTerms ←  groupTermsByArgs terms
  let gpPfs ←  groupProofsByArgs pfs
  let mut gpdDists : HashMap (List Name) ExprDist := HashMap.empty
  for (key, termarr) in gpTerms.toArray do
    for (x, w) in termarr do
      gpdDists :=  
        gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateTermM x w)
  for (key, pfarr) in gpPfs.toArray do
    for (l, pf, w) in pfarr do
      gpdDists :=  
        gpdDists.insert key (← (gpdDists.findD key ExprDist.empty).updateProofM l pf w)
  -- IO.println s!"{gpdDists.size} groups"
  flattenDists gpdDists

def existsM(dist: ExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      dist.proofsArr.anyM <| fun (l, _, w) => 
              do pure (decide <| w ≤ weight) <&&> isDefEq l prop
    else 
      dist.termsArr.anyM <| fun (t, w) => 
              do pure (decide <| w ≤ weight) <&&> isDefEq t elem

def existsPropM(dist: ExprDist)(prop: Expr)(weight: Nat) : TermElabM Bool :=
    dist.proofsArr.anyM <| fun (l, _, w) => 
              do 
              let res ←  pure (decide <| w ≤ weight) <&&> isDefEq l prop
              -- if res then 
              --   if !((← argList l) == (← argList prop)) then 
              --   IO.println s!"{l} = {prop} but {← argList l} != {← argList prop}"
              return res

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

def funcs(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let termFuncs ←   dist.termsArr.filterM $ fun (e, _) => 
       do Expr.isForall <| ← inferType e
    let pfFuncs ← dist.proofsArr.filterMapM <| fun (l, f, w) =>
      do if (← l.isForall) then some (f, w) else none
  return termFuncs ++ pfFuncs

def eqls(dist: ExprDist) : TermElabM (Array (Expr × Nat))  := do
  dist.proofsArr.filterMapM  $ fun (l, e, w) => 
       do if l.isEq then some (e, w) else none

def getProof?(dist: ExprDist)(prop: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  let opt ←  dist.proofsArr.findM? <| fun (l, p, w) => isDefEq l prop
  return opt.map <| fun (_, p, w) => (p, w)

def getTerm?(dist: ExprDist)(elem: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  dist.termsArr.findM? <| fun (t, w) => isDefEq t elem

def getGoals(dist: ExprDist)(goals : Array Expr) : TermElabM (Array (Expr × Expr × Nat )) := 
  do
    goals.filterMapM <| fun g => do 
      let wpf ← dist.getProof? g
      let wt ← dist.getTerm? g
      let res ←  wpf.orElse (fun _ => wt)
      return res.map (fun (x, w) => (g, x, w))

def viewGoals(dist: ExprDist)(goals : Array Expr) : TermElabM String :=
  do
    let pfs ← getGoals dist goals
    let view : Array String ←  pfs.mapM <| fun (g, pf, w) => do
      let stx ← delab (← getCurrNamespace) (← getOpenDecls) pf
      let fmt ← PrettyPrinter.ppTerm stx
      let pp ← fmt.pretty
      let stx ← delab (← getCurrNamespace) (← getOpenDecls) g
      let fmt ← PrettyPrinter.ppTerm stx
      let pg ← fmt.pretty
      s!"goal : {pg}\nproof: {pp}, weight : {w}"
    let s := view.foldl (fun acc e => acc ++ "\n" ++ e) "Proofs obtained:"
    return s

def coreView(l : TermElabM String) : CoreM  String := do

      let m := l.run'
      m.run'

def findD(dist: ExprDist)(elem: Expr)(default: Nat) : TermElabM Nat := do
  match ← getTerm? dist elem with
  | some (t, w) => pure w
  | none => pure default

end ExprDist

structure HashExprDist where
  termsMap : FinDist UInt64
  propsMap : FinDist UInt64

def ExprDist.hashDist(expr: ExprDist) : HashExprDist := 
  { termsMap := FinDist.fromArray (expr.termsArr.map <| fun (e, w) => (hash e, w)),
    propsMap := FinDist.fromArray (expr.proofsArr.map <| fun (l, e, w) => (hash e, w)) }

def HashExprDist.existsM(dist: HashExprDist)(elem: Expr)(weight: Nat) : TermElabM Bool :=
  do
    if ← isProof elem then
      let prop ← inferType elem
      dist.propsMap.exists (hash prop) weight
    else 
      dist.termsMap.exists (hash elem) weight
