import LeanLoris.FinDist
import LeanLoris.ExprDist
import LeanLoris.Core
import LeanLoris.ProdSeq
import Lean
import Lean.Meta
import Lean.Elab
import Std
open Lean
open Meta
open Elab
open Lean.PrettyPrinter
open Lean.Elab.Term
open Std
open Std.HashMap
open Nat
open ProdSeq

structure GeneratedDist where
  degree: Nat
  card : Option Nat
  exprDist : HashExprDist

class DataUpdate (D: Type) where
  update: ExprDist → Nat → Option Nat → D → D

def dataUpdate{D: Type}[du : DataUpdate D](d: ExprDist)(degBnd: Nat)(card: Option Nat) : D → D :=
  du.update d degBnd card

def idUpate{D: Type} : DataUpdate D :=
  ⟨fun _ _ _ d => d⟩

instance : DataUpdate Unit := idUpate 

instance : DataUpdate NameDist := idUpate

instance : NewElem Expr Unit := constNewElem (true, true)

instance {D: Type} : NewElem Name D := constNewElem (false, true)

class GetNameDist (D: Type) where
  nameDist: D → NameDist

def nameDist{D: Type}[c: GetNameDist D] : D  → NameDist :=
  c.nameDist

instance : GetNameDist NameDist := ⟨fun nd => nd⟩

instance : GetNameDist Unit := ⟨fun _ => FinDist.empty⟩

instance : NewElem Expr NameDist := constNewElem (true, true)

class DistHist (D: Type) where
  distHist: D → List GeneratedDist
  extDists : D → List HashExprDist


def newElemFromHistory {D: Type}[cl: DistHist D] : NewElem Expr D :=
  ⟨fun d  e deg => do
    let exst ← ((cl.distHist d).anyM <| fun dist =>  dist.exprDist.existsM e deg)
    let extrn ← ((cl.extDists d).anyM <| fun dist =>  dist.existsM e deg)
    return (!exst, !extrn)⟩

instance {D: Type}[cl: DistHist D] : NewElem Expr D := newElemFromHistory 

class IsleData(D: Type) where
  isleData : D → ExprDist → Nat → Option Nat → D

def isleData{D: Type}[c: IsleData D] : D → ExprDist → Nat → Option Nat → D := c.isleData

def idIsleData{D:Type} : IsleData D := ⟨fun d _ _ _=> d⟩

instance : IsleData Unit := idIsleData

instance : IsleData NameDist := idIsleData

abbrev FullData := NameDist × (List GeneratedDist) × (List HashExprDist)

instance : DistHist FullData := ⟨fun (nd, hist, ehist) => hist,
                                fun (nd, hist, ehist) => ehist⟩

instance : GetNameDist FullData := ⟨fun (nd, _) => nd⟩

instance : DataUpdate FullData := ⟨fun d deg c (nd, hist, ehist) => 
                                                        (nd, [⟨deg, c, d.hashDist⟩], ehist)⟩

instance : IsleData FullData :=
  ⟨fun ⟨nd, hist, ehist⟩ d deg c => (nd, [⟨deg, c, d.hashDist⟩], [d.hashDist])⟩ 

-- same signature for full evolution and single step, with ExprDist being initial state or accumulated state and the degree bound that for the result or the accumulated state
def Evolver(D: Type) : Type := (degreeBound: Nat) → (cardBound: Option Nat) →  ExprDist  → (initData: D) → ExprDist

def initEvolver(D: Type) : Evolver D := fun _ _ init _ => init

-- can again play two roles; and is allowed to depend on a generator; fixed-point should only be used for full generation, not for single step.
def RecEvolver(D: Type) : Type := (degreeBound: Nat) → (cardBound: Option Nat) →  ExprDist → (initData: D) → (evo: Evolver D) → ExprDist

instance{D: Type} : Inhabited <| Evolver D := ⟨initEvolver D⟩

partial def RecEvolver.fixedPoint{D: Type}(recEv: RecEvolver D) : Evolver D :=
        fun d c init memo => recEv d c init  memo (fixedPoint recEv)

-- same signature for full evolution and single step, with ExprDist being initial state or accumulated state and the degree bound that for the result or the accumulated state
def EvolverM(D: Type) : Type := (degreeBound: Nat) → (cardBound: Option Nat) →  (initData: D) → ExprDist  → TermElabM ExprDist


-- like EvolverM, can  play two roles; and is allowed to depend on a generator; fixed-point should only be used for full generation, not for single step.
def RecEvolverM(D: Type) : Type := (degreeBound: Nat) → (cardBound: Option Nat) →  ExprDist → (initData: D) → (evo: EvolverM D) → TermElabM ExprDist

namespace EvolverM

def init(D: Type) : EvolverM D := fun _ _ _ init  => pure init

def tautRec{D: Type}(ev: EvolverM D) : RecEvolverM D := 
        fun degBnd cb init d _ => ev degBnd cb d init 

def andThenM{D: Type}(ev : EvolverM D) 
              (effect: ExprDist → TermElabM Unit) : EvolverM D := 
      fun degBnd cb initDist data  => 
        do
          let newDist ← ev degBnd cb initDist data 
          effect newDist
          pure newDist

def merge{D: Type}(fst snd : EvolverM D) : EvolverM D :=
  fun degBnd cb initDist data => do
    (← fst degBnd cb initDist data) ++ (← snd degBnd cb initDist data)

def evolveAux{D: Type}[DataUpdate D](ev : EvolverM D)(incWt accumWt : Nat)
                    (cardBound: Option Nat) : 
                     ExprDist → (initData: D) →  TermElabM ExprDist := 
                     match incWt with
                     | 0 => fun initDist _ _ => return initDist
                     | m + 1 => fun initDist d  => 
                      do
                        let newDist ← ev (accumWt + 1) cardBound d initDist 
                        let newData := dataUpdate initDist accumWt cardBound d
                        evolveAux ev m (accumWt + 1) cardBound newDist newData 

def evolve{D: Type}[DataUpdate D](ev: EvolverM D) : EvolverM D :=
       fun degBnd cb initDist data  => 
        evolveAux ev degBnd 0 cb data initDist 

end EvolverM


instance{D: Type} : Inhabited <| EvolverM D := ⟨EvolverM.init D⟩
namespace RecEvolverM

def init(D: Type) := (EvolverM.init D).tautRec

partial def fixedPoint{D: Type}(recEv: RecEvolverM D) : EvolverM D :=
        fun degBnd c data init => recEv degBnd c init data (fixedPoint recEv)

def evolve{D: Type}[DataUpdate D](recEv: RecEvolverM D) : EvolverM D :=
       recEv.fixedPoint.evolve

def conjApply{D: Type}(recEv: RecEvolverM D)(ev: EvolverM D) : EvolverM D :=
        fun degBnd c data init => recEv degBnd c init data ev

def iterateAux{D: Type}[DataUpdate D](stepEv : RecEvolverM D)(incWt accumWt: Nat)
                    (cardBound: Option Nat) : 
                     ExprDist → (initData: D) → (evo: EvolverM D) → TermElabM ExprDist := 
                     match incWt with
                     | 0 => fun initDist _ _ => return initDist
                     | m + 1 => fun initDist d evo => 
                      do
                        IO.println s!"Evolver step: degree-bound = {accumWt+ 1}; cardinality-bound = {cardBound}; mono-time = {← IO.monoMsNow}"
                        IO.println s!"initial terms: {initDist.termsArray.size}, initial proofs: {initDist.proofsArray.size}"
                        let newDist ←  stepEv (accumWt + 1) cardBound initDist d evo
                        IO.println s!"step completed: degree-bound = {accumWt+ 1}; cardinality-bound = {cardBound}; mono-time = {← IO.monoMsNow}"
                        IO.println s!"final terms: {newDist.termsArray.size}, final proofs: {newDist.proofsArray.size}"
                        let newData := dataUpdate initDist accumWt cardBound d
                        iterateAux stepEv m (accumWt + 1) cardBound newDist newData evo

def iterate{D: Type}[DataUpdate D](stepEv : RecEvolverM D): RecEvolverM D := 
      fun degBnd cb initDist data evo => 
        iterateAux stepEv degBnd 0 cb initDist data evo

def levelIterate{D: Type}[DataUpdate D](stepEv : RecEvolverM D)
                    (steps maxDegree cardBound: Nat) : 
                     ExprDist → (initData: D) → (evo: EvolverM D) → TermElabM ExprDist := 
                     match steps with
                     | 0 => fun initDist _ _ => return initDist
                     | m + 1 => fun initDist d evo => 
                      do
                        let newDist ←  stepEv maxDegree cardBound initDist d evo
                        let newData := dataUpdate newDist  maxDegree cardBound d
                        levelIterate stepEv m maxDegree cardBound newDist newData evo

def merge{D: Type}(fst: RecEvolverM D)(snd: RecEvolverM D) : RecEvolverM D := 
      fun degBnd cb initDist data evo => 
        do
          let fstDist ← fst degBnd cb initDist data evo
          let sndDist ← snd degBnd cb initDist data evo
          fstDist ++ sndDist

def transformM{D: Type} (recEv : RecEvolverM D) 
            (f: ExprDist → TermElabM ExprDist) : RecEvolverM D := 
      fun degBnd cb initDist data evo => 
        do
          let newDist ← recEv degBnd cb initDist data evo
          f newDist

def andThenM{D: Type}(recEv : RecEvolverM D) 
              (effect: ExprDist → TermElabM Unit) : RecEvolverM D := 
      fun degBnd cb initDist data evo => 
        do
          let newDist ← recEv degBnd cb initDist data evo
          effect newDist
          pure newDist

end RecEvolverM

instance {D: Type}: Append <| RecEvolverM D := ⟨fun fst snd => fst.merge snd⟩

instance {D: Type}: Pow (EvolverM D) (RecEvolverM D) :=
  ⟨fun ev recEv => recEv.conjApply ev⟩

instance {D: Type}: Append <| EvolverM D := ⟨fun fst snd => fst.merge snd⟩

def isleM {D: Type}[IsleData D](type: Expr)(evolve : EvolverM D)(degreeBound: Nat)(cardBound: Option Nat)
      (init : ExprDist)(initData: D)(includePi : Bool := true)(excludeProofs: Bool := false)(excludeLambda : Bool := false)(excludeInit : Bool := false): TermElabM ExprDist := 
    withLocalDecl Name.anonymous BinderInfo.default (type)  $ fun x => 
        do
          let dist ←  init.updateExprM x 0
          let foldedFuncs : Array (Expr × Nat) ← 
            (← init.funcs).filterMapM (
              fun (f, deg) => do
                if !(f.isLambda) then pure none else
                  let y ← (mkApp? f x)
                  return y.map (fun y => (y, deg))
              )
          let dist ← dist.mergeArrayM foldedFuncs
          let purgedTerms ← dist.termsArray.filterM (fun (term, deg) => do
              match term with
              | Expr.lam _ t y _ => 
                let res ←  
                  try 
                    return !(← isType y <&&> isDefEq (← inferType x) t)
                  catch _ => pure true
                return res
              | _ => pure true
          )
          let dist := ⟨purgedTerms, dist.proofsArray⟩

          let eva ← evolve degreeBound cardBound  
                  (isleData initData dist degreeBound cardBound) dist
          let evb ← if excludeInit then eva.diffM dist else pure eva
          let innerTerms : Array (Expr × Nat) :=  if excludeProofs 
          then ← evb.termsArray.filterM ( fun (t, _) => do
              let b ← isDefEq t x
              return !b)
          else evb.termsArray
          let innerTypes ← innerTerms.filterM (fun (t, _) => liftMetaM (isType t))
          let lambdaTerms ← innerTerms.mapM (fun (t, deg) =>
              return (← mkLambdaFVars #[x] t, deg))  
          let piTypes ←  innerTypes.mapM (fun (t, deg) =>
              return (← mkForallFVars #[x] t, deg))
          let proofs ← evb.proofsArray.mapM (fun (prop, pf, deg) => do
            let expPf ← mkLambdaFVars #[x] pf
            let expPf ← whnf expPf
            Term.synthesizeSyntheticMVarsNoPostponing
            return (← inferType expPf , expPf , deg))
          let mut evl : ExprDist := ExprDist.empty
          let res := 
            ⟨if includePi then 
                if excludeLambda then piTypes else lambdaTerms ++ piTypes  
              else  lambdaTerms, if excludeProofs then #[] else proofs⟩
          return res

-- Some evolution cases; just one step (so update not needed)

def applyEvolver(D: Type)[NewElem Expr D] : EvolverM D := fun degBnd c d init => 
  do
    let res ← prodGenArrM apply? degBnd c (← init.funcs) init.allTermsArray d 
    return res

def applyPairEvolver(D: Type)[NewElem Expr D]: EvolverM D := 
  fun degBnd c d init =>
  do
    let funcs ← init.termsArray.filterM $ fun (e, _) => 
       do return Expr.isForall <| ← inferType e
    let pfFuncs ← init.proofsArray.filterMapM <| fun (l, f, deg) =>
      do if (l.isForall) then return some (f, deg) else return none
    let res ← tripleProdGenArrM applyPair? degBnd c 
          (← init.funcs) init.allTermsArray init.allTermsArray d
    return res

def simpleApplyEvolver(D: Type)[NewElem Expr D] : EvolverM D := fun degBnd c d init => 
  do
    /- for a given type α; functions with domain α and terms with type α  
    -/ 
    let mut grouped : HashMap UInt64 (Array (Expr × (Array (Expr  × Nat)) × (Array (Expr × Nat)))) 
        := HashMap.empty
    for (x, deg) in init.allTermsArray do
      let type ← whnf <| ← inferType x
      match type with
      | Expr.forallE _ dom b _ =>
          let key ← exprHash dom
          let arr := grouped.findD key #[] 
          match ← arr.findIdxM? <| fun (y, _, _) => isDefEq y dom with
          | some j =>
              let (y, fns, ts) := arr.get! j
              grouped := grouped.insert key (arr.set! j (y, fns.push (x, deg), ts))
          | none => 
              grouped := grouped.insert key (arr.push (dom, #[(x, deg)], #[]))
      |  _ => pure ()
      let key ← exprHash type
      let arr := grouped.findD key #[] 
      let dg := if (← isProof x) then 0 else deg
      match ← arr.findIdxM? <| fun (y, _, _) => isDefEq y type with
      | some j =>
              let (y, fns, ts) := arr.get! j
              grouped := grouped.insert key (arr.set! j (y, fns, ts.push (x, dg)))
      | none => 
              grouped := grouped.insert key (arr.push (type, #[], #[(x, dg)]))
    let mut cumPairCount : HashMap Nat Nat := HashMap.empty
    for (_, arr) in grouped.toArray do
      for (dom, fns, ts) in arr do
        for (f, wf) in fns do
          for (x, wx) in ts do
            let deg :=  wf + wx + 1
            for j in [deg: degBnd+ 1] do
            cumPairCount := cumPairCount.insert j (cumPairCount.findD j 0 + 1)
    let mut resTerms: Array (Expr × Nat) := #[]
    for (_, arr) in grouped.toArray do
      for (dom, fns, ts) in arr do
        for (f, wf) in fns do
          for (x, wx) in ts do
            let deg :=  wf + wx + 1
            if deg ≤ degBnd && (leqOpt (cumPairCount.findD deg 0)  c) then
              let y := mkApp f x
              let y ← whnf y
              Term.synthesizeSyntheticMVarsNoPostponing
              resTerms := resTerms.push (y, deg)
    let res ←  ExprDist.fromArrayM resTerms
    return res

def simpleApplyPairEvolver(D: Type)[NewElem Expr D]: EvolverM D := 
  fun degBnd c d init =>
  do
    let res ← tripleProdGenArrM mkAppPair? degBnd c 
          (← init.funcs) init.allTermsArray init.allTermsArray d
    return res

def nameApplyEvolver(D: Type)[GetNameDist D][NewElem Expr D]: EvolverM D := 
  fun degBnd c d init =>
  do
    let names := (nameDist d).toArray
    let res ← prodGenArrM nameApply? degBnd c names init.allTermsArray d
    return res

def nameApplyPairEvolver(D: Type)[GetNameDist D][NewElem Expr D]: 
        EvolverM D := fun degBnd c d init  =>
  do
    let names := (nameDist d).toArray
    let res ← tripleProdGenArrM nameApplyPair? degBnd c names init.allTermsArray init.allTermsArray d
    return res

def rewriteEvolver(D: Type)(flip: Bool := true)[NewElem Expr D] : EvolverM D := 
  fun degBnd c d init => 
  do
    prodGenArrM (rwPush? flip) degBnd c init.allTermsArray (← init.forallOfEquality) d

def congrEvolver(D: Type)[NewElem Expr D] : EvolverM D := 
  fun degBnd c d init  => 
  do
    prodGenArrM congrArg? degBnd c (← init.funcs) (← init.eqls) d

def eqIsleEvolver(D: Type)[NewElem Expr D][IsleData D] : RecEvolverM D := 
  fun degBnd c init d evolve => 
  do
    let mut eqTypesArr: Array (Expr × Nat) := Array.empty
    let mut eqs: ExprDist := ExprDist.empty -- equalities, degrees
    let mut eqTriples : Array (Expr × Expr × Nat) := #[] -- equality, lhs type, degree
    for (l, exp, deg) in init.proofsArray do
      match l.eq? with
      | none => pure ()
      | some (α, lhs, rhs) =>
          eqTypesArr := eqTypesArr.push (α, deg)
          eqs :=  eqs.pushProof l exp deg
          eqTriples := eqTriples.push (exp, α, deg)
    let eqsCum := degreeAbove eqs.allTermsArray degBnd
    let mut isleDistMap : HashMap Expr ExprDist := HashMap.empty
    let eqTypesExpr ←  ExprDist.fromArrayM eqTypesArr
    for (type, deg) in eqTypesExpr.termsArray do
      if degBnd - deg > 0 then
        let ic := c.map (fun x => x / (eqsCum.find! deg)) -- should not be missing
        let isleDist ←   isleM type evolve (degBnd -deg -1) ic init d false true false true
        isleDistMap := isleDistMap.insert type isleDist
    let finDistsAux : Array (Task (TermElabM ExprDist)) :=  
        (eqTriples.filter (fun (_, _, weq) => degBnd - weq > 0)).map <|
          fun (eq, type, weq) => 
          Task.spawn ( fun _ =>
            let isleDistBase := isleDistMap.findD type ExprDist.empty
            let xc := c.map (fun x => x / (eqsCum.find! weq)) -- should not be missing
            let isleDist := (isleDistBase.bound (degBnd -weq -1) xc).termsArray
            isleDist.foldlM (
                fun d (f, wf) => do 
                  match ← congrArg? f eq with 
                  | none => pure d
                  | some y => 
                      d.updateExprM y (wf + weq + 1)
                ) ExprDist.empty) 
    let finDists ← finDistsAux.mapM <| fun t => t.get
    let finDists := finDists.filter (fun d => d.termsArray.size > 0 || d.proofsArray.size > 0)
    let res := finDists.foldlM (fun x y => x ++ y) ExprDist.empty
    res

def allIsleEvolver(D: Type)[IsleData D] : RecEvolverM D := fun degBnd c init d evolve => 
  do
    let typeDist ← init.allSortsArray
    let typesCum := degreeAbove typeDist degBnd
    let mut finalDist: ExprDist := ExprDist.empty
    for (type, deg) in typeDist do
      if degBnd - deg > 0 then
        let ic := c.map <| fun x => x / (typesCum.find! deg)
        let isleDist ←   isleM type evolve (degBnd -deg -1) ic init d   
        finalDist ←  finalDist ++ isleDist
    return finalDist

def eqSymmTransEvolver (D: Type)(goalterms: Array Expr := #[]) : EvolverM D 
  := fun degBnd card d init => 
  do
    let mut eqs := ExprDist.empty -- new equations only
    let mut allEquationGroups : HashMap (UInt64) ExprDist := HashMap.empty
    -- let mut allEquations := ExprDist.empty
    -- initial equations
    for (l, pf, deg) in init.proofsArray do
      match l.eq? with
        | some (_, lhs, rhs) => if !(← isDefEq lhs rhs) then
          let key ← exprHash l
          allEquationGroups := allEquationGroups.insert key <|
              (allEquationGroups.findD key ExprDist.empty).pushProof l pf deg
        | none => pure ()
    -- symmetrize
    let eqnArray := allEquationGroups.toArray
    for (key, allEquations) in eqnArray do
      for (l, pf, deg) in allEquations.proofsArray do
        match l.eq? with
        | none => pure ()
        | some (_, lhs, rhs) =>
          let flipProp ← mkEq rhs lhs
          let flip ← whnf (← mkAppM ``Eq.symm #[pf])
          let flipkey ← exprHash flipProp
          match ← (allEquationGroups.findD flipkey ExprDist.empty).updatedProofM? 
                  flipProp flip (deg + 1) with
          | none => pure ()
          | some dist => 
            allEquationGroups := allEquationGroups.insert flipkey dist
            eqs := eqs.pushProof flipProp flip (deg + 1)
    /- group equations, for y we have proofs of x = y and then y = z,
        record array of (x, pf, deg) and array of (z, pf, z)
    -/
    let mut grouped : HashMap (UInt64)
          (Array (Expr × (Array (Expr × Expr × Nat)) × (Array (Expr × Expr × Nat)))) := 
      HashMap.empty
    for (key, allEquations) in allEquationGroups.toArray do
      for (l, pf, deg) in allEquations.proofsArray do
        match l.eq? with
        | none => pure ()
        | some (_, lhs, rhs) =>
          let lhs ← whnf lhs
          let rhs ← whnf rhs
          Term.synthesizeSyntheticMVarsNoPostponing
          -- update first component, i.e. y = rhs
          let key ← exprHash rhs
          match ← (grouped.findD key  #[]).findIdxM? <| fun (y, _, _) => isDefEq y rhs with
          | none => -- no equation involving rhs
            let degree := Nat.min deg (← init.findD lhs deg)
            grouped := grouped.insert key <|
              (grouped.findD key  #[]).push (rhs, #[(lhs, pf, degree)] , #[])
          | some j => 
            let (y, withRhs, withLhs) := (grouped.findD key  #[]).get! j
            -- if !((← exprHash rhs) = (← exprHash y)) then
            --   IO.println s!"Hash mismatch for \nrhs: {rhs}, \ny: {y};\nkey: {key}"
            let degree := Nat.min deg (← init.findD lhs deg)
            grouped := grouped.insert key <|
              (grouped.findD key  #[]).set! j (rhs, withRhs.push (lhs, pf, degree) , withLhs)
          -- update second component
          let key ← exprHash lhs
          match ← (grouped.findD key  #[]).findIdxM? <| fun (y, _, _) => isDefEq y lhs with
          | none => -- no equation involving lhs
            let degree := Nat.min deg (← init.findD rhs deg)
            grouped := grouped.insert key <|
              (grouped.findD key  #[]).push (lhs, #[], #[(rhs, pf, degree)])
          | some j => 
            let (y, withRhs, withLhs) := (grouped.findD key  #[]).get! j
            let degree := Nat.min deg (← init.findD rhs deg)
            grouped := grouped.insert key <|
              (grouped.findD key  #[]).set! j (lhs, withRhs, withLhs.push (rhs, pf, degree))
    -- count cumulative degrees of pairs, deleting reflexive pairs (assuming symmetry)
    let mut cumPairCount : HashMap Nat Nat := HashMap.empty
    for (key, group) in grouped.toArray do
      for (_, m ,_) in group do
        let degrees := m.map <| fun (_, _, deg) => deg
        for deg1 in degrees do
          for deg2 in degrees do 
            for j in [deg1 + deg2:degBnd + 1] do
              cumPairCount := cumPairCount.insert j (cumPairCount.findD j 0 + 1)
        for deg1 in degrees do 
          for j in [deg1 + deg1:degBnd + 1] do
            cumPairCount := cumPairCount.insert j (cumPairCount.findD j 0 - 1)
    for (key, group) in grouped.toArray do
      for (y, withRhs, withLhs) in group do
        for (x, eq1, deg1) in withRhs do
          for (z, eq2, deg2) in withLhs do
          let deg := deg1 + deg2
              -- if focus then IO.println s!"x: {x}, z: {z}, deg: {deg}" 
              if deg ≤ degBnd && (leqOpt (cumPairCount.findD deg 0)  card) then 
              unless ← isDefEq x  z do
                let eq3 ← whnf (←   mkAppM ``Eq.trans #[eq1, eq2]) 
                let prop ← mkEq x z
                Term.synthesizeSyntheticMVarsNoPostponing
                let key ← exprHash prop
                unless ← (allEquationGroups.findD key ExprDist.empty).existsPropM prop deg do
                  eqs := eqs.pushProof prop eq3 deg   
    return eqs


def funcDomIsleEvolver(D: Type)[IsleData D] : RecEvolverM D := fun degBnd c init d evolve => 
  do
    let mut typeDist := FinDist.empty
    for (x, deg) in init.allTermsArray do
      let type ← whnf (← inferType x)
      match type with
      | Expr.forallE _ t .. =>
          typeDist := typeDist.update type deg
      | _ => pure ()
    let typesCum := typeDist.cumulDegreeCount degBnd
    let mut finalDist: ExprDist := ExprDist.empty
    for (type, deg) in typeDist.toArray do
      if degBnd - deg > 0 then
        let ic := c.map <| fun x => x / (typesCum.findD deg 0)
        let isleDist ←   isleM type evolve (degBnd -deg -1) ic init d true false true  
        finalDist ←  finalDist ++ isleDist
    return finalDist

-- domains of terms (goals) that are pi-types, with minimum degree
def piDomains(terms: Array (Expr × Nat)) : TermElabM (Array (Expr × Nat)) := do
  let mut domains := Array.empty
  for (t, deg) in terms do
    match t with
    | Expr.forallE _ t .. =>
      match ← domains.findIdxM? <| fun (type, deg) => isDefEq type t with
      | some j =>
        let (type, degree) := domains.get! j
        if deg < degree then 
          domains := domains.set! j (t, deg) 
      | _ =>
        domains := domains.push (t, deg)
    | _ => pure ()
  return domains

-- generating from domains of pi-types
def introEvolverM(D: Type)[IsleData D](excludeInit: Bool := true) : RecEvolverM D := 
  fun degBnd c init d evolve => 
  -- if degBnd = 0 then init else
  do
    let piDoms ← piDomains (init.termsArray)
    let cumDegrees := FinDist.cumulDegreeCount  (FinDist.fromArray piDoms) degBnd
    let mut finalDist: ExprDist := ExprDist.empty
    for (type, deg) in piDoms do
      if deg ≤ degBnd && (leqOpt (cumDegrees.find! deg) c) then
      -- convert pi-types with given domain to lambdas
      let isleTerms ←  init.termsArray.mapM (fun (t, deg) => do 
          match t with
          | Expr.forallE _ l b _ =>
            if ← isDefEq l type then
              withLocalDecl Name.anonymous BinderInfo.default t  $ fun f =>
              withLocalDecl Name.anonymous BinderInfo.default l  $ fun x => do
                let y :=  mkApp f x
                let bt ← inferType y
                let t ← mkLambdaFVars #[x] bt
                let t ← whnf t
                Term.synthesizeSyntheticMVarsNoPostponing
                pure (t, deg)
            else
              pure (t, deg)
          | _ => pure (t, deg))
      let isleInit :=
          -- ←  ExprDist.fromArrayM isleTerms  
          ⟨isleTerms, init.proofsArray⟩
      let ic := c.map <| fun x => x / (cumDegrees.find! deg)
      let isleDist ←   isleM type evolve (degBnd ) ic isleInit 
                (isleData d init degBnd c) true false false excludeInit
      finalDist ←  finalDist ++ isleDist
    return finalDist

def degreeByType(cost: Nat): ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, deg) in init.termsArray do
    let α := ← whnf (← inferType x)
    match ← init.getTermM? α   with
    | some (_, deg)  => finalDist ←  ExprDist.updateTermM finalDist x (deg + cost)
    | _ => pure ()
  for (α , x, deg) in init.proofsArray do
    match ← init.getTermM? α  with
    | some (_, deg)  => finalDist ←  ExprDist.updateProofM finalDist α x (deg + cost)
    | _ => pure ()
  return finalDist

def refineDegree(degree? : Expr → TermElabM (Option Nat)):
      ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, deg) in init.termsArray do
    match ← degree? x   with
    | some deg  => finalDist ←  finalDist.updateTermM x (deg)
    | _ => pure ()
  for (prop, x, deg) in init.proofsArray do
    match ← degree? x   with
    | some deg  => finalDist ←  finalDist.updateProofM prop x (deg)
    | _ => pure ()
  return finalDist


def logResults(tk?: Option Syntax): Array Expr →  
  ExprDist →  TermElabM Unit := fun goals dist => do
    if tk?.isNone then
      IO.println "# Results of evolution step:\n"
      IO.println s!"* number of terms : {dist.termsArray.size}"
      IO.println s!"* number of proofs: {dist.proofsArray.size}\n"
    let mut count := 0
    for g in goals do
      count := count + 1
      if tk?.isNone then
        IO.println s!"- goal {count}: {← view g}"
      let statement ← (dist.allTermsArray.findM? $ fun (s, _) => isDefEq s g)
      if ← isProp g then
        if tk?.isNone then
          match statement with
          | some (s, deg) => 
            IO.println s!"  statement generated: ({← view s}, {deg})"
          | none => pure ()
        let proof ←  dist.proofsArray.findM? $ fun (l, t, deg) => 
                do isDefEq l g
        match proof with
        | some (_, pf, deg) =>
          match tk? with 
          | some tk => 
              logInfoAt tk m!"found proof {pf} for proposition goal {count} : {g}; degree {deg}"
          | none =>  
              IO.println s!"  proof generated: {← view pf}; degree: {deg}\n"
        | none =>  
          match tk? with 
          | some tk => 
              logWarningAt tk m!"no proof found for proposition goal {count} : {g}"
          | none =>  
              IO.println s!"  no proof found for goal {count}\n"         
          pure ()
      else
        match statement with
        | some (e, deg) =>
          match tk? with 
            | some tk => 
                logInfoAt tk m!"generated term {e} for goal {count} : {g}; degree: {deg}"
            | none =>            
                IO.println s!"  generated term: {← view e} for goal {count} : {g}; degree: {deg}"
        | none => 
          match tk? with 
          | some tk => 
            logWarningAt tk m!"no term found for goal {count} : {g}"
          | none => pure ()
          pure ()

abbrev EvolutionM := ExprDist → TermElabM ExprDist

def EvolutionM.followedBy(fst snd: EvolutionM): EvolutionM := fun dist => do
  let dist ← fst dist
  snd dist

instance : Mul EvolutionM := 
  ⟨fun fst snd => fst.followedBy snd⟩


