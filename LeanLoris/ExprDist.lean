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
          -- if !((← exprHash l) == (← exprHash prop)) then 
          --   IO.println s!"{l} = {prop} but {← exprHash l} != {← exprHash prop}"
          if w ≤ d then return m 
          else return ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updateTermM(m: ExprDist) (x: Expr) (d: Nat) : TermElabM ExprDist := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => isDefEq t x) with
      | some j =>
        let (t, w) := m.termsArr.get! j 
        -- if !((← exprHash x) == (← exprHash t)) then 
        --     IO.println s!"{x} = {t} but {← exprHash x} != {← exprHash t}"
        if w ≤ d then return m
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
          -- if !((← exprHash l) == (← exprHash prop)) then 
          --   IO.println s!"{l} = {prop} but {← exprHash l} != {← exprHash prop}"
          if w ≤ d then return none
          else return some ⟨m.termsArr, m.proofsArr.set! j (prop, x, d)⟩
      | none => 
        return some ⟨m.termsArr, m.proofsArr.push (prop, x, d)⟩

def updatedTermM?(m: ExprDist) (x: Expr) (d: Nat) : TermElabM (Option ExprDist) := 
  do
    match ← (m.termsArr.findIdxM? <| fun (t, w) => isDefEq t x) with
      | some j =>
        let (t, w) := m.termsArr.get! j 
        -- if !((← exprHash x) == (← exprHash t)) then 
        --     IO.println s!"{x} = {t} but {← exprHash x} != {← exprHash t}"
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

def groupTermsByArgs(terms : Array (Expr × Nat)) : 
      TermElabM (HashMap (UInt64) (Array (Expr × Nat))) := do
      terms.foldlM (fun m (e, w) => 
        do
          let key ← exprHash e
          return m.insert key ((m.findD key #[]).push (e, w))
          ) HashMap.empty

def groupProofsByArgs(proofs : Array (Expr × Expr × Nat)) : 
      TermElabM (HashMap (UInt64) (Array (Expr × Expr × Nat))) := do
      proofs.foldlM (fun m (l, pf, w) => 
        do
          let key ← exprHash l
          return m.insert key ((m.findD key #[]).push (l, pf, w))
          ) HashMap.empty

def groupDistByArgs(arr: Array (Expr × Nat)) : TermElabM (HashMap (UInt64) ExprDist) := do
  arr.foldlM (fun m (e, w) => do       
      if ← isProof e then
        let l ← inferType e
        let key ← exprHash l
        return m.insert key ((m.findD key ExprDist.empty).pushProof l e w)
        else 
        let key ← exprHash e
        return m.insert key ((m.findD key ExprDist.empty).pushTerm e w)
      ) HashMap.empty

def flattenDists(m: HashMap (UInt64) ExprDist) : TermElabM ExprDist := do
  let termArr := (m.toArray.map (fun (_, d) => d.termsArr)).foldl (fun a b => a.append b) Array.empty
  let pfArr := (m.toArray.map (fun (_, d) => d.proofsArr)).foldl (fun a b => a.append b) Array.empty
  -- IO.println s!"termList = {termList.length}"
  -- IO.println s!"pfList = {pfList.length}"
  return ⟨termArr, pfArr⟩

def mergeGroupedM(fst snd: ExprDist) : TermElabM ExprDist := do
    -- IO.println s!"merging; time: {← IO.monoMsNow}; sizes: ({fst.termsArr.size}, {fst.proofsArr.size}) ({snd.termsArr.size}, {snd.proofsArr.size})"
    let ⟨fstTerms, fstProofs⟩ := fst
    let mut gpFstTerms ←  groupTermsByArgs fstTerms
    let mut gpFstPfs ←  groupProofsByArgs fstProofs
    let mut ⟨sndTerms, sndProofs⟩ := ExprDist.empty
    -- IO.println s!"grouped first terms and proofs; groups: {gpFstTerms.size} {gpFstPfs.size}"
    for (prop, x, d) in snd.proofsArr do
      let key ← exprHash prop
      match ← ((gpFstPfs.findD key #[]).findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := (gpFstPfs.findD key #[]).get! j
          -- if !((← exprHash l) == (← exprHash prop)) then 
          --   IO.println s!"{l} = {prop} but {← exprHash l} != {← exprHash prop}"
          if w ≤ d then pure ()
          else 
           gpFstPfs := gpFstPfs.insert key <| (gpFstPfs.findD key #[]).eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArr do
      let key ← exprHash x
      match ← ((gpFstTerms.findD key #[]).findIdxM? <| fun (t, w) =>  isDefEq t x)  with
      | some j => 
          let (t, w) := (gpFstTerms.findD key #[]).get! j
          -- if !((← exprHash x) == (← exprHash t)) then 
          --   IO.println s!"{x} = {t} but {← exprHash x} != {← exprHash t}"
          if w ≤ d then pure ()
          else 
           gpFstTerms := gpFstTerms.insert key <| (gpFstTerms.findD key #[]).eraseIdx j 
           sndTerms := sndTerms.push (x, d)
      | none => 
          sndTerms := sndTerms.push (x, d)
    -- IO.println "added second terms and proofs"
    let mut gpdDists : HashMap (UInt64) ExprDist := HashMap.empty
    for (key, termarr) in gpFstTerms.toArray do
      for (x, w) in termarr do
        gpdDists :=  
          gpdDists.insert key ((gpdDists.findD key ExprDist.empty).pushTerm x w)
    for (key, pfarr) in gpFstPfs.toArray do
      for (l, pf, w) in pfarr do
        gpdDists :=  
          gpdDists.insert key ((gpdDists.findD key ExprDist.empty).pushProof l pf w)
    -- IO.println "created grouped dists; to flatten"
    let fstDist ←  flattenDists gpdDists
    let res := ⟨fstDist.termsArr ++ sndTerms, fstDist.proofsArr ++ sndProofs⟩
    -- IO.println s!"merged arrays obtained; time: {← IO.monoMsNow}; size: {fstTerms.size + sndTerms.size}; {fstProofs.size + sndProofs.size}"
    return res

def diffM(fst snd: ExprDist) : TermElabM ExprDist := do
    -- IO.println s!"merging; time: {← IO.monoMsNow}; sizes: ({fst.termsArr.size}, {fst.proofsArr.size}) ({snd.termsArr.size}, {snd.proofsArr.size})"
    let ⟨sndTerms, sndProofs⟩ := snd
    let gpTerms ←  groupTermsByArgs sndTerms
    let gpPfs ←  groupProofsByArgs sndProofs
    let filteredTerms ←  fst.termsArr.filterM (fun (x, w) => do
           let key ←  exprHash x
           let found ← 
              (gpTerms.findD key #[]).anyM (fun (y, w') => (isDefEq x y) <&&> (return w' ≤ w))
           return !found)
    let filteredProofs ←  fst.proofsArr.filterM (fun (x, _, w) => do
          let key ←  exprHash x
          let found ← (gpPfs.findD key #[]).anyM (fun (y, _, w') => (isDefEq x y) <&&> (return w' ≤ w))
          return !found)
    return ⟨filteredTerms, filteredProofs⟩

def mergeM(fst snd: ExprDist) : TermElabM ExprDist := do
    -- logInfo m!"merging; time: {← IO.monoMsNow}; sizes: ({fst.termsArr.size}, {fst.proofsArr.size}) ({snd.termsArr.size}, {snd.proofsArr.size})"
    let mut ⟨fstTerms, fstProofs⟩ := fst
    let mut ⟨sndTerms, sndProofs⟩ := ExprDist.empty
    for (prop, x, d) in snd.proofsArr do
      let key ← exprHash prop
      match ← (fstProofs.findIdxM? <| fun (l, _, w) =>  isDefEq l prop)  with
      | some j => 
          let (l, p, w) := fstProofs.get! j
          -- if !((← exprHash l) == (← exprHash prop)) then 
          --   IO.println s!"{l} = {prop} but {← exprHash l} != {← exprHash prop}"
          if w ≤ d then pure ()
          else 
           fstProofs := fstProofs.eraseIdx j 
           sndProofs := sndProofs.push (prop, x, d)
      | none => 
          sndProofs := sndProofs.push (prop, x, d)
    for (x, d) in snd.termsArr do
      let key ← exprHash x
      match ← (fstTerms.findIdxM? <| fun (t, w) =>  isDefEq t x)  with
      | some j => 
          let (t, w) := fstTerms.get! j
          -- if !((← exprHash x) == (← exprHash t)) then 
          --   IO.println s!"{x} = {t} but {← exprHash x} != {← exprHash t}"
          if w ≤ d then pure ()
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
  let mut gpdDists : HashMap (UInt64) ExprDist := HashMap.empty
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

def mergeArray(fst: ExprDist)(arr: Array (Expr× Nat)): TermElabM ExprDist := do 
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
  let ⟨fstTerms, fstProofs⟩ := fst
    let mut gpFstTerms ←  groupTermsByArgs fstTerms
    let mut gpFstPfs ←  groupProofsByArgs fstProofs
  let mut gpdDists : HashMap (UInt64) ExprDist := HashMap.empty
  for (key, termarr) in gpFstTerms.toArray do
    gpdDists := gpdDists.insert key ⟨termarr, #[]⟩
  for (key, pfsArr) in gpFstPfs.toArray do
    gpdDists := gpdDists.insert key ⟨
        (gpdDists.findD key ExprDist.empty).termsArr, pfsArr⟩
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
              --   if !((← exprHash l) == (← exprHash prop)) then 
              --   IO.println s!"{l} = {prop} but {← exprHash l} != {← exprHash prop}"
              return res

def terms(dist: ExprDist) : FinDist Expr := 
      FinDist.fromArray dist.termsArr

def allTermsArr(dist: ExprDist) : Array (Expr × Nat) :=
  dist.termsArr ++ 
          (dist.proofsArr.map <| fun (_, t, w) => (t, w))

def allTerms(dist: ExprDist) : FinDist Expr := 
      FinDist.fromArray (dist.termsArr ++ 
          (dist.proofsArr.map <| fun (_, t, w) => (t, w)))

def allSorts(dist: ExprDist) : TermElabM (FinDist Expr) := do
  let types ←  dist.termsArr.filterM <| fun (e, w) => do
          return (← inferType e).isSort
  let props := dist.proofsArr.map <| fun (l, _, w) => (l, w)
  return FinDist.fromArray <| types ++ props

def bound(dist: ExprDist)(wb cb: Nat) : ExprDist := Id.run do
  let mut cumCount : HashMap Nat Nat := HashMap.empty
  for (_, w) in dist.termsArr do
      for j in [w:wb + 1] do
        cumCount := cumCount.insert j (cumCount.findD j 0 + 1)
  for (_, _, w) in dist.proofsArr do
      for j in [w:wb + 1] do
        cumCount := cumCount.insert j (cumCount.findD j 0 + 1)
  ⟨dist.termsArr.filter fun (_, w) => w ≤ wb && cumCount.find! w ≤ cb,
    dist.proofsArr.filter fun (_, _, w) => w ≤ wb && cumCount.find! w ≤ cb⟩
  

def typesArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  dist.termsArr.filterM <| fun (e, w) => do
   isType e

def propsArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  dist.termsArr.filterM <| fun (e, w) => do
   isProp e

def funcs(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  let termFuncs ←   dist.termsArr.filterM $ fun (e, _) => 
       do return Expr.isForall <| ← inferType e
    let pfFuncs ← dist.proofsArr.filterMapM <| fun (l, f, w) =>
      do if (l.isForall) then return some (f, w) else return none
  return termFuncs ++ pfFuncs

def eqls(dist: ExprDist) : TermElabM (Array (Expr × Nat))  := do
  dist.proofsArr.filterMapM  $ fun (l, e, w) => 
       do if l.isEq then return some (e, w) else return none

def eventuallyEquality(l: Expr): Bool := 
  if l.isEq then true
  else 
    match l with
       | Expr.forallE _ _ b _  => eventuallyEquality b
       | _ => false

def eventuallyEqls(dist: ExprDist) : TermElabM (Array (Expr × Nat))  := do
  dist.proofsArr.filterMapM  $ fun (l, e, w) => 
       if eventuallyEquality l then return some (e, w) else return none

def getProof?(dist: ExprDist)(prop: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  let opt ←  dist.proofsArr.findM? <| fun (l, p, w) => isDefEq l prop
  return opt.map <| fun (_, p, w) => (p, w)

def hasProof(dist: ExprDist)(prop: Expr) : TermElabM Bool := do
  dist.proofsArr.anyM <| fun (l, _, _) => isDefEq l prop

def goalsArr(dist: ExprDist) : TermElabM (Array (Expr × Nat)) := do
  (← dist.propsArr).filterM <| fun (e, w) => do
    return !(← dist.hasProof e)

def getTerm?(dist: ExprDist)(elem: Expr) : TermElabM (Option (Expr ×  Nat)) := do
  dist.termsArr.findM? <| fun (t, w) => isDefEq t elem

def getGoals(dist: ExprDist)(goals : Array Expr)(showStatement: Bool := false) : 
  TermElabM (Array (Expr × Expr × Nat )) := 
  do
    goals.filterMapM <| fun g => do 
      let wpf ← dist.getProof? g
      let wt ← dist.getTerm? g
      let res := if (showStatement) then wpf.orElse (fun _ => wt) else wpf
      return res.map (fun (x, w) => (g, x, w))

def viewGoals(dist: ExprDist)(goals : Array Expr)(showStatement: Bool := false) 
    : TermElabM String :=
  do
    let pfs ← dist.getGoals goals showStatement
    let view : Array String ←  pfs.mapM <| fun (g, pf, w) => do
      return s!"goal : {← view g}\nproof: {← view pf}, weight : {w}"
    let s := view.foldl (fun acc e => acc ++ "\n" ++ e) "Proofs obtained:"
    return s

def coreView(l : TermElabM String) : CoreM  String := do
      let m := l.run'
      m.run'

def findD(dist: ExprDist)(elem: Expr)(default: Nat) : TermElabM Nat := do
  match ← getTerm? dist elem with
  | some (t, w) => pure w
  | none => pure default

def mapM(dist: ExprDist)(f: Expr → TermElabM Expr) : TermElabM ExprDist := do
  let termsArrBase ← dist.allTermsArr.mapM <| fun (e, n) => do
    let e ← f e
    return (e, n)
  fromArray termsArrBase


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
      return dist.propsMap.exists (hash prop) weight
    else 
      return dist.termsMap.exists (hash elem) weight
