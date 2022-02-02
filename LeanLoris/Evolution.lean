import LeanLoris.FinDist
import LeanLoris.ExprDist
import LeanLoris.Core
import LeanLoris.ProdSeq
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
open ProdSeq

structure GenDist where
  weight: Nat
  card : Nat
  exprDist : ExprDist

class DataUpdate (D: Type) where
  update: ExprDist → Nat → Nat → D → D

def dataUpdate{D: Type}[du : DataUpdate D](d: ExprDist)(wb card: Nat) : D → D :=
  du.update d wb card

def idUpate{D: Type} : DataUpdate D :=
  ⟨fun _ _ _ d => d⟩

instance : DataUpdate Unit := idUpate 

instance : DataUpdate NameDist := idUpate

class IsNew (D: Type) where
  isNew: D → Nat → Nat →  Expr → Nat →  TermElabM Bool
  isNewPair : D → Nat → Nat →  Expr → Nat →  Expr → Nat → TermElabM Bool
  isNewTriple : D → Nat → Nat →  Expr → Nat →  Expr → Nat → Expr → Nat →   TermElabM Bool

def isNew{D: Type}[c: IsNew D] : D → Nat → Nat →   Expr  → Nat  → TermElabM Bool :=
  c.isNew

def allNew{D: Type} : IsNew D :=
  ⟨fun d _ _ e _ => true, fun d _ _ _ _ _ _  => true,
  fun _ _ _ _ _ _ _ _ _ => true⟩

instance : IsNew Unit := allNew

instance : NewElem Expr Unit := constNewElem (true, true)

instance {D: Type} : NewElem Name D := constNewElem (false, true)

def isNewPair{D: Type}[c: IsNew D] : D → Nat → Nat →  
        (Expr ×   Expr) → (Nat × Nat)  → TermElabM Bool :=
  fun d wb cb (e1, e2) (w1, w2) => c.isNewPair d wb cb e1 w1 e2 w2

class GetNameDist (D: Type) where
  nameDist: D → NameDist

def nameDist{D: Type}[c: GetNameDist D] : D  → NameDist :=
  c.nameDist

instance : GetNameDist NameDist := ⟨fun nd => nd⟩

instance : GetNameDist Unit := ⟨fun _ => FinDist.empty⟩

instance : IsNew NameDist := allNew

instance : NewElem Expr NameDist := constNewElem (true, true)

class DistHist (D: Type) where
  distHist: D → List GenDist
  extHist : D → List ExprDist

def newFromHistory {D: Type}[cl: DistHist D] : IsNew D :=
  ⟨fun d wb c e w => do
    let exs ← ((cl.distHist d).anyM <| fun dist =>  dist.exprDist.existsM e w)
    return !exs,
  fun d wb c e1 w1 e2 w2 => do
    let exs ← ((cl.distHist d).anyM <| fun ⟨wt, _,dist⟩ => 
      dist.existsM e1 w1 <&&> (dist.existsM e2 w2) <&&> (w1 + w2 + 1 ≤ wt))
    return !exs,
    fun d wb c e1 w1 e2 w2 e3 w3 => do
    let exst ← ((cl.distHist d).anyM <| fun ⟨wt, _,dist⟩ => do
      dist.existsM e1 w1 <&&> (dist.existsM e2 w2) <&&> (dist.existsM e3 w3) <&&>
    (w1 + w2 + w3 + 1 ≤ wt))
     return !exst⟩

def newElemFromHistory {D: Type}[cl: DistHist D] : NewElem Expr D :=
  ⟨fun d  e w => do
    let exst ← ((cl.distHist d).anyM <| fun dist =>  dist.exprDist.existsM e w)
    let extrn ← ((cl.extHist d).anyM <| fun dist =>  dist.existsM e w)
    return (!exst, !extrn)⟩

instance {D: Type}[cl: DistHist D] : IsNew D := newFromHistory 

instance {D: Type}[cl: DistHist D] : NewElem Expr D := newElemFromHistory 

class IsleData(D: Type) where
  isleData : D → ExprDist → Nat → Nat → D

def isleData{D: Type}[c: IsleData D] : D → ExprDist → Nat → Nat → D := c.isleData

def idIsleData{D:Type} : IsleData D := ⟨fun d _ _ _=> d⟩

instance : IsleData Unit := idIsleData

instance : IsleData NameDist := idIsleData

abbrev FullData := NameDist × (List GenDist) × (List ExprDist)

instance : DistHist FullData := ⟨fun (nd, hist, ehist) => hist,
                                fun (nd, hist, ehist) => ehist⟩

instance : GetNameDist FullData := ⟨fun (nd, _) => nd⟩

instance : DataUpdate FullData := ⟨fun d w c (nd, hist, ehist) => 
                                                        (nd, [⟨w, c, d⟩], ehist)⟩

instance : IsleData FullData :=
  ⟨fun ⟨nd, hist, ehist⟩ d w c => (nd, [⟨w, c, d⟩], [d])⟩ 

-- same signature for full evolution and single step, with ExprDist being initial state or accumulated state and the weight bound that for the result or the accumulated state
def Evolution(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist  → (initData: D) → ExprDist

def initEvolution(D: Type) : Evolution D := fun _ _ init _ => init

-- can again play two roles; and is allowed to depend on a generator; fixed-point should only be used for full generation, not for single step.
def RecEvolver(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist → (initData: D) → (evo: Evolution D) → ExprDist

instance{D: Type} : Inhabited <| Evolution D := ⟨initEvolution D⟩

partial def RecEvolver.fixedPoint{D: Type}(recEv: RecEvolver D) : Evolution D :=
        fun d c init memo => recEv d c init  memo (fixedPoint recEv)

-- same signature for full evolution and single step, with ExprDist being initial state or accumulated state and the weight bound that for the result or the accumulated state
def EvolutionM(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist  → (initData: D) → TermElabM ExprDist


-- like EvolutionM, can  play two roles; and is allowed to depend on a generator; fixed-point should only be used for full generation, not for single step.
def RecEvolverM(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist → (initData: D) → (evo: EvolutionM D) → TermElabM ExprDist

namespace EvolutionM

def init(D: Type) : EvolutionM D := fun _ _ init _ => pure init

def tautRec{D: Type}(ev: EvolutionM D) : RecEvolverM D := 
        fun wb cb init d _ => ev wb cb init d

def andThenM{D: Type}(ev : EvolutionM D) 
              (effect: ExprDist → TermElabM Unit) : EvolutionM D := 
      fun wb cb initDist data  => 
        do
          let newDist ← ev wb cb initDist data 
          effect newDist
          newDist

end EvolutionM


instance{D: Type} : Inhabited <| EvolutionM D := ⟨EvolutionM.init D⟩

namespace RecEvolverM

def init(D: Type) := (EvolutionM.init D).tautRec

partial def fixedPoint{D: Type}(recEv: RecEvolverM D) : EvolutionM D :=
        fun d c init memo => recEv d c init memo (fixedPoint recEv)

def iterateAux{D: Type}[DataUpdate D](stepEv : RecEvolverM D)(incWt accumWt cardBound: Nat) : 
                     ExprDist → (initData: D) → (evo: EvolutionM D) → TermElabM ExprDist := 
                     match incWt with
                     | 0 => fun initDist _ _ => return initDist
                     | m + 1 => fun initDist d evo => 
                      do
                        let newDist ←  stepEv (accumWt + 1) cardBound initDist d evo
                        let newData := dataUpdate initDist accumWt cardBound d
                        iterateAux stepEv m (accumWt + 1) cardBound newDist newData evo

def iterate{D: Type}[DataUpdate D](stepEv : RecEvolverM D): RecEvolverM D := 
      fun wb cb initDist data evo => 
        iterateAux stepEv wb 0 cb initDist data evo

def levelIterate{D: Type}[DataUpdate D](stepEv : RecEvolverM D)
                    (steps maxWeight cardBound: Nat) : 
                     ExprDist → (initData: D) → (evo: EvolutionM D) → TermElabM ExprDist := 
                     match steps with
                     | 0 => fun initDist _ _ => return initDist
                     | m + 1 => fun initDist d evo => 
                      do
                        let newDist ←  stepEv maxWeight cardBound initDist d evo
                        let newData := dataUpdate newDist  maxWeight cardBound d
                        levelIterate stepEv m maxWeight cardBound newDist newData evo

def merge{D: Type}(fst: RecEvolverM D)(snd: RecEvolverM D) : RecEvolverM D := 
      fun wb cb initDist data evo => 
        do
          let fstDist ← fst wb cb initDist data evo
          let sndDist ← snd wb cb initDist data evo
          fstDist ++ sndDist

def transformM{D: Type} (recEv : RecEvolverM D) 
            (f: ExprDist → TermElabM ExprDist) : RecEvolverM D := 
      fun wb cb initDist data evo => 
        do
          let newDist ← recEv wb cb initDist data evo
          f newDist

def andThenM{D: Type}(recEv : RecEvolverM D) 
              (effect: ExprDist → TermElabM Unit) : RecEvolverM D := 
      fun wb cb initDist data evo => 
        do
          let newDist ← recEv wb cb initDist data evo
          effect newDist
          newDist

end RecEvolverM

instance {D: Type}: Append <| RecEvolverM D := ⟨fun fst snd => fst.merge snd⟩

def EvolutionM.evolve{D: Type}[DataUpdate D](ev: EvolutionM D) : EvolutionM D :=
        ev.tautRec.iterate.fixedPoint

def isleM {D: Type}[IsleData D](type: Expr)(evolve : EvolutionM D)(weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D)(includePi : Bool := true)(excludeProofs: Bool := false)(excludeLambda : Bool := false)(excludeConstants : Bool := false): TermElabM (ExprDist) := 
    withLocalDecl Name.anonymous BinderInfo.default (type)  $ fun x => 
        do
          let dist ←  init.updateExprM x 0
          -- logInfo m!"initial in isle: {l}"
          let evb ← evolve weightBound cardBound dist 
                  (isleData initData dist weightBound cardBound) 
          let mut evl : ExprDist := ExprDist.empty
          for (y, w) in evb.termsArr do
            unless excludeProofs && (← isProof y) ||
            (excludeConstants && (← init.existsM y w)) do
              evl ←  ExprDist.updateExprM evl y w
          let evt ← evl.termsArr.filterM (fun (x, _) => liftMetaM (isType x))
          let exported ← evl.mapM (fun e => mkLambdaFVars #[x] e)
          let fe := FinDist.fromArray <|
                   ← evt.mapM (fun (e, w) => do pure ( ← mkForallFVars #[x] e, w))
          let exportedPi : ExprDist := ⟨fe, HashMap.empty⟩ -- pi-types are never proofs
          let res := 
            if includePi then 
                if excludeLambda then exportedPi else ← exported ++ exportedPi 
              else  exported
          return res

-- Some evolution cases; just one step (so update not needed)

def applyEvolver(D: Type)[NewElem Expr D] : EvolutionM D := fun wb c init d => 
  do
    -- logInfo m!"apply evolver started, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    let funcs ← init.termsArr.filterM $ fun (e, _) => 
       do Expr.isForall <| ← inferType e
    let pfFuncs ← init.proofsArr.filterMapM <| fun (l, f, w) =>
      do if (← l.isForall) then some (f, w) else none
    let res ← prodGenArrM applyOpt wb c (funcs ++ pfFuncs) init.termsArr d 
    -- logInfo m!"apply evolver finished, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    return res

def applyPairEvolver(D: Type)[cs : IsNew D][NewElem Expr D]: EvolutionM D := 
  fun wb c init d =>
  do
    -- logInfo m!"apply pair evolver started, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    let funcs ← init.termsArr.filterM $ fun (e, _) => 
       do Expr.isForall <| ← inferType e
    let pfFuncs ← init.proofsArr.filterMapM <| fun (l, f, w) =>
      do if (← l.isForall) then some (f, w) else none
    let res ← tripleProdGenArrM applyPairOpt wb c 
          (funcs ++ pfFuncs) init.termsArr init.termsArr d
    -- logInfo m!"apply pair evolver finished, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    return res

def nameApplyEvolver(D: Type)[IsNew D][GetNameDist D][NewElem Expr D]: EvolutionM D := fun wb c init d =>
  do
    -- logInfo m!"name apply evolver started, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    let names := (nameDist d).toArray
    let res ← prodGenArrM nameApplyOpt wb c names init.termsArr d
    -- logInfo m!"name apply evolver finished, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    return res

def nameApplyPairEvolver(D: Type)[cs: IsNew D][GetNameDist D][NewElem Expr D]: 
        EvolutionM D := fun wb c init d =>
  do
    -- logInfo m!"name apply pair evolver started, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    let names := (nameDist d).toArray
    let res ← tripleProdGenArrM nameApplyPairOpt wb c names init.termsArr init.termsArr d
    -- logInfo m!"name apply pair evolver finished, wb: {wb}, c: {c}, time: {← IO.monoMsNow}"
    return res

def rewriteEvolver(flip: Bool)(D: Type)[IsNew D][NewElem Expr D] : EvolutionM D := 
  fun wb c init d => 
  do
    let eqls ←  init.proofsArr.filterMapM  $ fun (l, e, w) => 
       do if l.isEq then some (e, w) else none
    prodGenArrM (rwPushOpt flip) wb c init.termsArr eqls d

def congrEvolver(D: Type)[IsNew D][NewElem Expr D] : EvolutionM D := fun wb c init d => 
  do
    let funcs ←   init.termsArr.filterM $ fun (e, _) => 
       do Expr.isForall <| ← inferType e
    let pfFuncs ← init.proofsArr.filterMapM <| fun (l, f, w) =>
      do if (← l.isForall) then some (f, w) else none
    let eqls  ←  init.proofsArr.filterMapM  $ fun (l, e, w) => 
       do if l.isEq then some (e, w) else none
    prodGenArrM congrArgOpt wb c (funcs ++ pfFuncs) eqls d

def eqIsleEvolver(D: Type)[IsNew D][NewElem Expr D][IsleData D] : RecEvolverM D := 
  fun wb c init d evolve => 
  do
    -- logInfo m!"isle called: weight-bound {wb}, cardinality: {c}"
    -- logInfo m!"initial time: {← IO.monoMsNow}"
    let mut eqTypes: FinDist Expr := FinDist.empty -- lhs types, (minimum) weights
    let mut eqs: FinDist Expr := FinDist.empty -- equalities, weights
    let mut eqTriples : Array (Expr × Expr × Nat) := #[] -- equality, lhs type, weight
    for (l, exp, w) in init.proofsArr do
      match l.eq? with
      | none => ()
      | some (α, lhs, rhs) =>
          eqTypes ←  eqTypes.update α w
          eqs ←  eqs.update exp w
          eqTriples := eqTriples.push (exp, α, w)
    let eqsCum := eqs.cumulWeightCount wb
    let mut isleDistMap : HashMap Expr ExprDist := HashMap.empty
    -- logInfo m!"equality types: {eqTypes.size}"
    for (type, w) in eqTypes.toArray do
      if wb - w > 0 then
        let ic := c / (eqsCum.find! w) -- should not be missing
        let isleDist ←   isleM type evolve (wb -w -1) ic init d false true false true
        isleDistMap := isleDistMap.insert type isleDist
    -- logInfo m!"tasks to be defined :{← IO.monoMsNow}"
    let finDistsAux : Array (Task (TermElabM ExprDist)) :=  
        (eqTriples.filter (fun (_, _, weq) => wb - weq > 0)).map <|
          fun (eq, type, weq) => 
          Task.spawn ( fun _ =>
            let isleDistBase := isleDistMap.findD type ExprDist.empty
            let xc := c / (eqsCum.find! weq) -- should not be missing
            let isleDist := isleDistBase.terms.bound (wb -weq -1) xc
            isleDist.toArray.foldlM (
                fun d (f, wf) => do 
                  match ← congrArgOpt f eq with 
                  | none => d
                  | some y => 
                      d.updateExprM y (wf + weq + 1)
                ) ExprDist.empty) 
    -- logInfo m!"tasks defined :{← IO.monoMsNow}"
    let finDists ← finDistsAux.mapM <| fun t => t.get
    -- logInfo m!"tasks executed :{← IO.monoMsNow}"
    let res := finDists.foldlM (fun x y => x ++ y) ExprDist.empty
    -- logInfo m!"isle done: {← IO.monoMsNow}"
    res

def allIsleEvolver(D: Type)[IsNew D][IsleData D] : RecEvolverM D := fun wb c init d evolve => 
  do
    let typeDist ← init.allSorts
    let typesCum := typeDist.cumulWeightCount wb
    let mut finalDist: ExprDist := ExprDist.empty
    for (type, w) in typeDist.toArray do
      if wb - w > 0 then
        let ic := c / (typesCum.find! w)
        let isleDist ←   isleM type evolve (wb -w -1) ic init d   
        finalDist ←  finalDist ++ isleDist
    return finalDist

def eqSymmTransEvolver (D: Type)[IsNew D](goalterms: Array Expr := #[]) : EvolutionM D 
  := fun wb card init d => 
  do
    logInfo m!"eqSymmTrans called: weight-bound {wb}, cardinality: {card}"
    logInfo m!"initial terms: {init.termsMap.size}"
    logInfo m!"initial proofs: {init.proofsMap.size}"
    let mut eqs := ExprDist.empty -- new equations only
    let mut allEquations := ExprDist.empty
    -- initial equations
    for (l, pf, w) in init.proofsArr do
      match l.eq? with
        | some (_, lhs, rhs) => if !(lhs == rhs) then  
          allEquations := allEquations.pushProof l pf w
        | none => ()
    -- symmetrize
    for (l, pf, w) in allEquations.proofsArr do
      match l.eq? with
      | none => ()
      | some (_, lhs, rhs) =>
        let flipProp ← mkEq rhs lhs
        let flip ← whnf (← mkAppM ``Eq.symm #[pf])
        match ← allEquations.updatedProofM? flipProp flip (w + 1) with
        | none => ()
        | some dist => 
          allEquations := dist
          eqs ← eqs.pushProof flipProp flip (w + 1)
    /- group equations, for y we have proofs of x = y and then y = z,
        record array of (x, pf, w) and array of (z, pf, z)
    -/
    let mut grouped : 
          HashMap Expr <| (Array (Expr × Expr × Nat)) × (Array (Expr × Expr × Nat)) := 
              HashMap.empty
    for (l, pf, w) in allEquations.proofsArr do
      match l.eq? with
      | none => ()
      | some (_, lhs, rhs) =>
        -- update first component, i.e. y = rhs
        match ← grouped.find?  rhs with
        | none => -- no equation involving rhs
          let weight := Nat.min w (init.terms.findD lhs w)
          grouped := grouped.insert rhs (#[(lhs, pf, weight)], #[])
        | some (withRhs, withLhs) => 
          let weight := Nat.min w (init.terms.findD lhs w)
          grouped := grouped.insert rhs (withRhs.push (lhs, pf, weight), withLhs)
        -- update second component
        match ← grouped.find?  lhs with
        | none => -- no equation involving lhs
          let weight := Nat.min w (init.terms.findD rhs w)
          grouped := grouped.insert lhs (#[], #[(rhs, pf, weight)])
        | some (withRhs, withLhs) =>
          let weight := Nat.min w (init.terms.findD rhs w)
          grouped := grouped.insert lhs (withRhs, withLhs.push (rhs, pf, weight))
    -- count cumulative weights of pairs, deleting reflexive pairs (assuming symmetry)
    let mut cumPairCount : HashMap Nat Nat := HashMap.empty
    for (y, m ,_) in grouped.toArray do
      -- if m.size > 1 then logInfo m!"{y} is in {m.size} equations"
      let weights := m.map <| fun (_, _, w) => w
      for w1 in weights do
        for w2 in weights do 
          for j in [w1 + w2 +1:wb + 1] do
            cumPairCount := cumPairCount.insert j (cumPairCount.findD j 0 + 1)
      for w1 in weights do 
        for j in [w1 + w1 + 1:wb + 1] do
          cumPairCount := cumPairCount.insert j (cumPairCount.findD j 0 - 1)
    logInfo m!"cumulative pair count: {cumPairCount.toArray}"
    for g in goalterms do
      logInfo m!"goalterm: {g}, {grouped.find? g}, {init.terms.find? g}" 
      logInfo m!"{← init.termsArr.findM? <| fun (t, w) => isDefEq t g}"
    for (y, withRhs, withLhs) in grouped.toArray do
      for (x, eq1, w1) in withRhs do
        for (z, eq2, w2) in withLhs do
        let w := w1 + w2 + 1
            if w ≤ wb && (cumPairCount.findD w 0) ≤ card * 2 then 
            unless x == z do
              let eq3 ← whnf (←   mkAppM ``Eq.trans #[eq1, eq2]) 
              let prop ← mkEq x z
              Term.synthesizeSyntheticMVarsNoPostponing
              unless ← allEquations.existsPropM prop w do
                eqs ← eqs.pushProof prop eq3 w   
    return eqs


def funcDomIsleEvolver(D: Type)[IsNew D][IsleData D] : RecEvolverM D := fun wb c init d evolve => 
  do
    let mut typeDist := FinDist.empty
    for (x, w) in init.termsArr do
      let type ← whnf (← inferType x)
      match type with
      | Expr.forallE _ t .. =>
          typeDist ←  typeDist.update type w
      | _ => ()
    let typesCum := typeDist.cumulWeightCount wb
    let mut finalDist: ExprDist := ExprDist.empty
    for (type, w) in typeDist.toArray do
      if wb - w > 0 then
        let ic := c / (typesCum.findD w 0)
        let isleDist ←   isleM type evolve (wb -w -1) ic init d true false true  
        finalDist ←  finalDist ++ isleDist
    return finalDist

def weightByType(cost: Nat): ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, w) in init.termsArr do
    let α := ← whnf (← inferType x)
    match ← init.termsMap.find? α   with
    | some w  => finalDist ←  ExprDist.updateTermM finalDist x (w + cost)
    | _ => ()
  for (α , x, w) in init.proofsArr do
    match ← init.termsMap.find? α  with
    | some w  => finalDist ←  ExprDist.updateProofM finalDist α x (w + cost)
    | _ => ()
  return finalDist

def refineWeight(weight? : Expr → TermElabM (Option Nat)):
      ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, w) in init.termsArr do
    match ← weight? x   with
    | some w  => finalDist ←  finalDist.updateTermM x (w)
    | _ => ()
  for (prop, x, w) in init.proofsArr do
    match ← weight? x   with
    | some w  => finalDist ←  finalDist.updateProofM prop x (w)
    | _ => ()
  return finalDist

def logResults(goals : Array Expr) : ExprDist →  TermElabM Unit := fun dist => do
    logInfo m!"number of terms : {dist.termsArr.size}"
    logInfo m!"number of proofs: {dist.proofsArr.size}"
    for g in goals do
      logInfo m!"goal: {g}"
      let statement ←  (dist.termsArr.findM? $ fun (s, _) => isDefEq s g)
      let statement ←  statement.mapM $ fun (e, w) => do (← whnf e, w) 
      if ← isProp g then
        logInfo m!"proposition generated: {← statement}"
        let proof ←  dist.proofsArr.findM? $ fun (l, t, w) => 
                do isDefEq l g
        logInfo m!"proof generated: {proof}"
      else
        logInfo m!"term generated: {statement}"

-- examples

def egEvolver : EvolutionM Unit := 
  ((applyEvolver Unit).tautRec ++ (RecEvolverM.init Unit)).fixedPoint

def egEvolverFull : EvolutionM FullData := 
  ((applyEvolver FullData).tautRec ++ (RecEvolverM.init FullData)).fixedPoint


declare_syntax_cat evolver 
syntax "app" : evolver
syntax "name-app": evolver
syntax "binop": evolver
syntax "name-binop": evolver
syntax "rewrite": evolver
syntax "rewrite-flip": evolver
syntax "congr": evolver
syntax "eq-isles": evolver
syntax "all-isles": evolver
syntax "func-dom-isles": evolver
syntax "eq-closure": evolver
syntax "eq-closure" (expr_list)?: evolver

declare_syntax_cat evolve_transformer
syntax "by-type" (num)?: evolve_transformer

declare_syntax_cat evolver_list
syntax "^[" evolver,* (">>" evolve_transformer)? "]" : evolver_list

def parseEvolver : Syntax → TermElabM (RecEvolverM FullData)
| `(evolver|app) => (applyEvolver FullData).tautRec
| `(evolver|name-app) => (nameApplyEvolver FullData).tautRec
| `(evolver|binop) => (applyPairEvolver FullData).tautRec
| `(evolver|name-binop) => (nameApplyPairEvolver FullData).tautRec
| `(evolver|rewrite) => (rewriteEvolver true FullData).tautRec
| `(evolver|rewrite-flip) => (rewriteEvolver false FullData).tautRec
| `(evolver|congr) => (congrEvolver FullData).tautRec
| `(evolver|eq-isles) => eqIsleEvolver FullData
| `(evolver|all-isles) => allIsleEvolver FullData
| `(evolver|func-dom-isles) => funcDomIsleEvolver FullData
| `(evolver|eq-closure) => (eqSymmTransEvolver FullData).tautRec
| `(evolver|eq-closure $goals) => do
        let goals ← parseExprList goals
        (eqSymmTransEvolver FullData goals).tautRec

| stx => throwError m!"Evolver not implemented for {stx}"

def parseEvolverTrans : Syntax → TermElabM (ExprDist → TermElabM ExprDist)
| `(evolve_transformer|by-type) => return weightByType 1
| `(evolve_transformer|by-type $n) => do
      let n ← parseNat n
      return weightByType n
| stx => throwError m!"Evolver transformer not implemented for {stx}"


def parseEvolverList : Syntax → TermElabM (RecEvolverM FullData)  
  | `(evolver_list|^[$[$xs],*]) =>
    do
          let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
          return m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)
  | `(evolver_list|^[$[$xs],* >> $tr]) =>
    do
          let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
          return (m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)).transformM 
                    <| ← parseEvolverTrans tr
  | _ => throwIllFormedSyntax

syntax (name:= evolution) 
  "evolve!" evolver_list (expr_list)? expr_dist (name_dist)? num num  : term
@[termElab evolution] def evolutionImpl : TermElab := fun s _ =>
match s with
| `(evolve! $evolvers $(goals?)? $initDist $(nameDist?)? $wb $card) => do
  let ev ← parseEvolverList evolvers
  let initDist ← parseExprMap initDist
  let initDist := FinDist.fromList (initDist.toList)
  let nameDist? ← nameDist?.mapM  $ fun nameDist => parseNameMap nameDist
  let nameDist := nameDist?.getD #[]
  let nameDist := FinDist.fromList (nameDist.toList)
  let initData : FullData := (nameDist, [], [])
  let goals? ← goals?.mapM $ fun goals => parseExprList goals
  let goals := goals?.getD #[]
  let ev := ev.fixedPoint.evolve.andThenM (logResults goals)
  let wb ← parseNat wb
  let card ← parseNat card
  let finalDist ← ev wb card (← ExprDist.fromTermsM initDist) initData
  let reportDist ← finalDist.terms.filterM <| fun e => do
    goals.anyM $ fun g => do
      isDefEq e g <||>  isDefEq (← inferType e) g
  return ← (ppackWeighted reportDist.toList)
| _ => throwIllFormedSyntax

def syn: MacroM Syntax :=  `(evolver|app)
#check syn.run

def syn2: TermElabM Syntax :=  `(evolver_list|^[app, name-app])
#check syn2.run
def lstfromsyn:  TermElabM (RecEvolverM FullData)  :=  do
        let syn ← syn2
        parseEvolverList syn

#check lstfromsyn

def tup : Nat × Nat × Nat := (1, (2, 3)) 