import LeanLoris.FinDist
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
  isNew: D → Nat → Nat →  Expr → Nat →  Bool

def isNew{D: Type}[c: IsNew D] : D → Nat → Nat →   Expr  → Nat  → Bool :=
  c.isNew

def allNew{D: Type} : IsNew D :=
  ⟨fun d _ _ e _ => true⟩

instance : IsNew Unit := allNew

def isNewPair{D: Type}[c: IsNew D] : D → Nat → Nat →  
        (Expr ×   Expr) → (Nat × Nat)  → Bool :=
  fun d wb cb (e1, e2) (w1, w2) => isNew d wb cb e1 w1 || isNew d wb cb e2 w2

class GetNameDist (D: Type) where
  nameDist: D → NameDist

def nameDist{D: Type}[c: GetNameDist D] : D  → NameDist :=
  c.nameDist

instance : GetNameDist NameDist := ⟨fun nd => nd⟩

instance : GetNameDist Unit := ⟨fun _ => FinDist.empty⟩

class DistHist (D: Type) where
  distHist: D → List GenDist

def newFromHistory {D: Type}[cl: DistHist D] : IsNew D :=
  ⟨fun d wb c e w =>
    let hist := (cl.distHist d).filter <| fun gd => wb ≤ gd.weight  && c ≤  gd.card  
    hist.any <| fun dist =>  dist.exprDist.exists e w⟩

instance {D: Type}[cl: DistHist D] : IsNew D := newFromHistory 

abbrev FullData := NameDist × (List GenDist)

instance : DistHist FullData := ⟨fun (nd, hist) => hist⟩

instance : GetNameDist FullData := ⟨fun (nd, _) => nd⟩

instance : DataUpdate FullData := ⟨fun d w c (nd, hist) => (nd, ⟨w, c, d⟩ :: hist)⟩

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


-- can again play two roles; and is allowed to depend on a generator; fixed-point should only be used for full generation, not for single step.
def RecEvolverM(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist → (initData: D) → (evo: EvolutionM D) → TermElabM ExprDist

namespace EvolutionM

def init(D: Type) : EvolutionM D := fun _ _ init _ => pure init

def tautRec{D: Type}(ev: EvolutionM D) : RecEvolverM D := 
        fun wb cb init d _ => ev wb cb init d

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
                        let newData := dataUpdate newDist  (accumWt + 1) cardBound d
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
          return fstDist ++ sndDist

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

def isleM {D: Type}(type: Expr)(evolve : EvolutionM D)(weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D)(includePi : Bool := true)(excludeProofs: Bool := false)(excludeLambda : Bool := false): TermElabM (ExprDist) := 
    withLocalDecl Name.anonymous BinderInfo.default (type)  $ fun x => 
        do
          let dist := init.insert x 0
          -- logInfo m!"initial in isle: {l}"
          let evb ← evolve weightBound cardBound dist initData 
          let mut evl : ExprDist := FinDist.empty
          for (y, w) in evb.toArray do
            unless excludeProofs && ((← inferType (← inferType y)).isProp) do
              evl := FinDist.update evl y w
          let evt ← evl.filterM (fun x => liftMetaM (isType x))
          let exported ← evl.mapM (fun e => mkLambdaFVars #[x] e)
          let exportedPi ← evt.mapM (fun e => mkForallFVars #[x] e)
          let res := 
            if includePi then 
                if excludeLambda then exportedPi else  exported ++  exportedPi 
              else  exported
          return res

-- Some evolution cases; just one step (so update not needed)

def applyEvolver(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let funcs ← init.filterM $ fun e => 
       do Expr.isForall <| ← inferType e
    prodGenM applyOpt wb c funcs init (isNewPair d)

def applyPairEvolver(D: Type)[IsNew D]: EvolutionM D := fun wb c init d =>
  do
    let funcs ← init.filterM $ fun e => 
       do Expr.isForall <| ← inferType e
    tripleProdGenM applyPairOpt wb c funcs init init (
          fun wb c (f, x, y) (wf, wx, wy) => 
            isNew d wb c f wf || isNew d wb c x wx || isNew d wb c y wy)

def nameApplyEvolver(D: Type)[IsNew D][GetNameDist D]: EvolutionM D := fun wb c init d =>
  do
    let names := nameDist d
    prodGenM nameApplyOpt wb c names init (
          fun wb c (_, e) (_, we) => 
            isNew d wb c e we)
    

def nameApplyPairEvolver(D: Type)[IsNew D][GetNameDist D]: EvolutionM D := fun wb c init d =>
  do
    let names := nameDist d
    tripleProdGenM nameApplyPairOpt wb c names init init (
          fun wb c (_, x, y) (_, wx, wy) => 
            isNewPair d wb c (x, y) (wx, wy))
    

def rewriteEvolver(flip: Bool)(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let eqls ←   init.filterM  $ fun e => 
       do Expr.isEq <| ← inferType e
    prodGenM (rwPushOpt flip) wb c init eqls (isNewPair d)

def congrEvolver(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let funcs ←   init.filterM $ fun e => 
       do Expr.isForall <| ← inferType e
    let eqls ←   init.filterM $ fun e => 
       do Expr.isEq <| ← inferType e
    prodGenM congrArgOpt wb c funcs eqls (isNewPair d)

def eqIsleEvolver(D: Type)[IsNew D] : RecEvolverM D := fun wb c init d evolve => 
  do
    let mut eqTypes: ExprDist := FinDist.empty
    let mut eqs: ExprDist := FinDist.empty
    let mut eqTriples : Array (Expr × Expr × Nat) := #[]
    for (x, w) in init.toArray do
      match (← inferType x).eq? with
      | none => ()
      | some (α, lhs, rhs) =>
          eqTypes := FinDist.update eqTypes α w
          eqs := FinDist.update eqs x w
          eqTriples := eqTriples.push (x, α, w)
    let typesCum := eqTypes.cumulWeightCount
    let eqsCum := eqs.cumulWeightCount
    let typesTop := (typesCum.toList.map (fun (k, v) => v)).maximum?.getD 1
    let eqsTop := (typesCum.toList.map (fun (k, v) => v)).maximum?.getD 1
    let mut isleDistMap : HashMap Expr ExprDist := HashMap.empty
    for (type, w) in eqTypes.toArray do
      if wb - w > 0 then
        let ic := c / (typesCum.findD w typesTop)
        let isleDist ←   isleM type evolve (wb -w -1) ic init d false true
        isleDistMap := isleDistMap.insert type isleDist
    let mut finalDist: ExprDist := FinDist.empty
    for (eq, type, weq) in eqTriples do
      if wb - weq > 0 then
        let isleDistBase := isleDistMap.findD type FinDist.empty
        let xc := c / (eqsCum.findD weq eqsTop)
        let isleDist := isleDistBase.bound (wb -weq -1) xc
        for (f, wf) in isleDist.toArray do
          match ← congrArgOpt f eq with 
          | none => ()
          | some y => finalDist := finalDist.insert y (wf + weq)
    return finalDist

def allIsleEvolver(D: Type)[IsNew D] : RecEvolverM D := fun wb c init d evolve => 
  do
    let typeDist ← init.filterM $ fun e =>
        do return (← inferType e).isSort 
    let typesCum := typeDist.cumulWeightCount
    let typesTop := (typesCum.toList.map (fun (k, v) => v)).maximum?.getD 1
    let mut finalDist: ExprDist := FinDist.empty
    for (type, w) in typeDist.toArray do
      if wb - w > 0 then
        let ic := c / (typesCum.findD w typesTop)
        let isleDist ←   isleM type evolve (wb -w -1) ic init d   
        finalDist := finalDist ++ isleDist
    return finalDist

def funcDomIsleEvolver(D: Type)[IsNew D] : RecEvolverM D := fun wb c init d evolve => 
  do
    let mut typeDist := FinDist.empty
    for (x, w) in init.toArray do
      match ← whnf (← inferType x) with
      | Expr.forallE _ t .. =>
          typeDist := FinDist.update typeDist (← whnf (← inferType t)) w
      | _ => ()
    let typesCum := typeDist.cumulWeightCount
    let typesTop := (typesCum.toList.map (fun (k, v) => v)).maximum?.getD 1
    let mut finalDist: ExprDist := FinDist.empty
    for (type, w) in typeDist.toArray do
      if wb - w > 0 then
        let ic := c / (typesCum.findD w typesTop)
        let isleDist ←   isleM type evolve (wb -w -1) ic init d true false true  
        finalDist := finalDist ++ isleDist
    return finalDist

def weightByType(cost: Nat): ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, w) in init.toArray do
    let α := ← whnf (← inferType x)
    match init.find? α   with
    | some w  => finalDist := FinDist.update finalDist x (w + cost)
    | _ => ()
  return finalDist

def refineWeight(weight? : Expr → TermElabM (Option Nat)):
      ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, w) in init.toArray do
    match ← weight? x   with
    | some w  => finalDist := FinDist.update finalDist x (w)
    | _ => ()
  return finalDist

def logResults(goals : List Expr) : ExprDist →  TermElabM Unit := fun dist => do
    for g in goals do
      logInfo m!"goal: {g}"
      let statement ←  dist.findM? $ fun s => isDefEq s g
      logInfo m!"statement: {statement}"
      let proof ←  dist.findM? $ fun t => do isDefEq (← inferType t) g
      logInfo m!"proof: {proof}"

-- syntax for getting expressions; first an auxiliarly function

def initializedEvolve (goals: List Expr)(initDist : ExprDist): (initNames: NameDist) →  
            (stepEv : RecEvolverM FullData) → Nat → Nat → TermElabM ExprDist := 
  fun initNames stepEv wb c  => do
    let initData : FullData := (initNames, [])   
    let evolver : EvolutionM FullData := (stepEv.andThenM (logResults goals)).fixedPoint     
    evolver wb c initDist initData 
  
  
-- examples

def egEvolver : EvolutionM Unit := 
  ((applyEvolver Unit).tautRec ++ (RecEvolverM.init Unit)).fixedPoint

