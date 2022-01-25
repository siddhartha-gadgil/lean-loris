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
  isNew: D → Nat → Nat →  Expr → Nat →  TermElabM Bool
  isNewPair : D → Nat → Nat →  Expr → Nat →  Expr → Nat → TermElabM Bool
  isNewTriple : D → Nat → Nat →  Expr → Nat →  Expr → Nat → Expr → Nat →   TermElabM Bool

def isNew{D: Type}[c: IsNew D] : D → Nat → Nat →   Expr  → Nat  → TermElabM Bool :=
  c.isNew

def allNew{D: Type} : IsNew D :=
  ⟨fun d _ _ e _ => true, fun d _ _ _ _ _ _  => true,
  fun _ _ _ _ _ _ _ _ _ => true⟩

instance : IsNew Unit := allNew

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

class DistHist (D: Type) where
  distHist: D → List GenDist

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

def isleM {D: Type}(type: Expr)(evolve : EvolutionM D)(weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D)(includePi : Bool := true)(excludeProofs: Bool := false)(excludeLambda : Bool := false)(excludeConstants : Bool := false): TermElabM (ExprDist) := 
    withLocalDecl Name.anonymous BinderInfo.default (type)  $ fun x => 
        do
          let dist ←  init.updateExprM x 0
          -- logInfo m!"initial in isle: {l}"
          let evb ← evolve weightBound cardBound dist initData 
          let mut evl : ExprDist := ExprDist.empty
          for (y, w) in evb.terms.toArray do
            unless excludeProofs && (← isProof y) ||
            (excludeConstants && (← init.existsM y w)) do
              evl ←  ExprDist.updateExprM evl y w
          let evt ← evl.terms.filterM (fun x => liftMetaM (isType x))
          let exported ← evl.mapM (fun e => mkLambdaFVars #[x] e)
          let exportedPi : ExprDist :=
                ⟨← evt.mapM (fun e => mkForallFVars #[x] e), HashMap.empty⟩
          let res := 
            if includePi then 
                if excludeLambda then exportedPi else ←  exported ++  exportedPi 
              else  exported
          return res

-- Some evolution cases; just one step (so update not needed)

def applyEvolver(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let funcs ← init.terms.filterM $ fun e => 
       do Expr.isForall <| ← inferType e
    prodGenM applyOpt wb c funcs init.terms (isNewPair d)

def applyPairEvolver(D: Type)[cs : IsNew D]: EvolutionM D := fun wb c init d =>
  do
    let funcs ← init.terms.filterM $ fun e => 
       do Expr.isForall <| ← inferType e
    tripleProdGenM applyPairOpt wb c funcs init.terms init.terms (
          fun wb c (f, x, y) (wf, wx, wy) => 
            cs.isNewTriple d wb c f wf x wx y wy)

def nameApplyEvolver(D: Type)[IsNew D][GetNameDist D]: EvolutionM D := fun wb c init d =>
  do
    let names := nameDist d
    prodGenM nameApplyOpt wb c names init.terms (
          fun wb c (_, e) (_, we) => 
            isNew d wb c e we)
    

def nameApplyPairEvolver(D: Type)[cs: IsNew D][GetNameDist D]: EvolutionM D := fun wb c init d =>
  do
    let names := nameDist d
    tripleProdGenM nameApplyPairOpt wb c names init.terms init.terms (
          fun wb c (_, x, y) (_, wx, wy) => 
            isNewPair d wb c (x, y) (wx, wy))
    

def rewriteEvolver(flip: Bool)(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let eqls ←   init.terms.filterM  $ fun e => 
       do Expr.isEq <| ← inferType e
    prodGenM (rwPushOpt flip) wb c init.terms eqls (isNewPair d)

def congrEvolver(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let funcs ←   init.terms.filterM $ fun e => 
       do Expr.isForall <| ← inferType e
    let eqls ←   init.terms.filterM $ fun e => 
       do Expr.isEq <| ← inferType e
    prodGenM congrArgOpt wb c funcs eqls (isNewPair d)

def eqIsleEvolver(D: Type)[IsNew D] : RecEvolverM D := fun wb c init d evolve => 
  do
    logInfo m!"isle called: weight-bound {wb}, cardinality: {c}"
    let mut eqTypes: ExprDist := ExprDist.empty -- lhs types, (minimum) weights
    let mut eqs: ExprDist := ExprDist.empty -- equalities, weights
    let mut eqTriples : Array (Expr × Expr × Nat) := #[] -- equality, lhs type, weight
    for (exp, w) in init.terms.toArray do
      match (← inferType exp).eq? with
      | none => ()
      | some (α, lhs, rhs) =>
          eqTypes ←  ExprDist.updateExprM eqTypes α w
          eqs ←  ExprDist.updateExprM eqs exp w
          eqTriples := eqTriples.push (exp, α, w)
    let eqsCum := eqs.terms.cumulWeightCount wb
    let mut isleDistMap : HashMap Expr ExprDist := HashMap.empty
    for (type, w) in eqTypes.terms.toArray do
      if wb - w > 0 then
        let ic := c / (eqsCum.findD w 0) -- should not be 0
        let isleDist ←   isleM type evolve (wb -w -1) ic init d false true false true
        isleDistMap := isleDistMap.insert type isleDist
    let mut finalDist: ExprDist := ExprDist.empty
    for (eq, type, weq) in eqTriples do
      if wb - weq > 0 then
        let isleDistBase := isleDistMap.findD type ExprDist.empty
        let xc := c / (eqsCum.findD weq 0) -- should not be 0
        let isleDist := isleDistBase.terms.bound (wb -weq -1) xc
        for (f, wf) in isleDist.toArray do
          match ← congrArgOpt f eq with 
          | none => ()
          | some y => finalDist ←  finalDist.updateExprM y (wf + weq + 1)
    return finalDist

def allIsleEvolver(D: Type)[IsNew D] : RecEvolverM D := fun wb c init d evolve => 
  do
    let typeDist ← init.terms.filterM $ fun e =>
        do return (← inferType e).isSort 
    let typesCum := typeDist.cumulWeightCount wb
    let typesTop := (typesCum.toList.map (fun (k, v) => v)).maximum?.getD 1
    let mut finalDist: ExprDist := ExprDist.empty
    for (type, w) in typeDist.toArray do
      if wb - w > 0 then
        let ic := c / (typesCum.findD w typesTop)
        let isleDist ←   isleM type evolve (wb -w -1) ic init d   
        finalDist ←  finalDist ++ isleDist
    return finalDist

def eqSymmTransEvolver (D: Type)[IsNew D] : EvolutionM D := fun wb card init d => 
do
    logInfo m!"eqSymmTrans called: weight-bound {wb}, cardinality: {card}"
    let mut eqs := ExprDist.empty
    let mut pfs : HashMap (Expr × Expr) Expr := HashMap.empty
    -- group by lhs
    let mut provedEqual : HashMap Expr (FinDist Expr) := HashMap.empty
    -- initial equalities
    for (e, w) in init.terms.toArray do
      match (← inferType e).eq? with
      | none => ()
      | some (α , lhs, rhs) => 
        unless lhs == rhs do
        let lhsMap := provedEqual.findD lhs (FinDist.empty)
        provedEqual := provedEqual.insert lhs (lhsMap.update rhs w) 
        pfs := pfs.insert (lhs, rhs) e
        eqs ← eqs.updateExprM e w -- original to avoid complicated proofs
    logInfo m!"initial equalities: {eqs.terms.toArray.size}"
    -- symmetrize
    let initeqs := provedEqual.toArray
    for (lhs, m) in initeqs do
      for (rhs, w) in m.toArray do
        let rhsMap := provedEqual.findD rhs (FinDist.empty)
        unless rhsMap.exists lhs w do
          provedEqual := provedEqual.insert rhs (rhsMap.insert lhs w)
          let pf := pfs.find! (lhs, rhs) 
          let flip ← whnf (← mkAppM ``Eq.symm #[pf])
          Term.synthesizeSyntheticMVarsNoPostponing
          pfs := pfs.insert (rhs, lhs) flip
          eqs ← eqs.updateExprM flip w
    logInfo m!"equalities after flip: {eqs.terms.toArray.size}"
    -- count cumulative weights of pairs, deleting reflexive pairs
    let mut cumPairCount : HashMap Nat Nat := HashMap.empty
    for (lhs, m) in provedEqual.toArray do
      let weights := m.toArray.map <| fun (_, w) => w
      for w1 in weights do
        for w2 in weights do 
          for j in [w1 + w2 +1:wb + 1] do
            cumPairCount := cumPairCount.insert j (cumPairCount.findD j 0 + 1)
      for w1 in weights do 
        for j in [w1 + w1 + 1:wb + 1] do
          cumPairCount := cumPairCount.insert j (cumPairCount.findD j 0 - 1)
    logInfo m!"cumulative pair count: {cumPairCount.toArray}"
    -- make equations by transitivity
    for (lhs, m) in provedEqual.toArray do
      for (rhs1, w1) in m.toArray do
        let rhsMap := provedEqual.findD rhs1 (FinDist.empty)
        for (rhs2, w2) in rhsMap.toArray do
          unless rhs2 == lhs do
            let w := w1 + w2 + 1
            if w ≤ wb && (cumPairCount.findD w 0) ≤ card * 2 then 
              let eq1 := pfs.find! (lhs, rhs1)
              let eq2 := pfs.find! (rhs1, rhs2)
              let eq3 ← whnf (←   mkAppM ``Eq.trans #[eq1, eq2]) 
              Term.synthesizeSyntheticMVarsNoPostponing
              eqs ← eqs.updateExprM eq3 w
    logInfo m!"equalities after transitivity: {eqs.terms.toArray.size}"
    return eqs


def funcDomIsleEvolver(D: Type)[IsNew D] : RecEvolverM D := fun wb c init d evolve => 
  do
    let mut typeDist := ExprDist.empty
    for (x, w) in init.terms.toArray do
      match ← whnf (← inferType x) with
      | Expr.forallE _ t .. =>
          typeDist ←  ExprDist.updateExprM typeDist (← whnf (← inferType t)) w
      | _ => ()
    let typesCum := typeDist.terms.cumulWeightCount wb
    let typesTop := (typesCum.toList.map (fun (k, v) => v)).maximum?.getD 1
    let mut finalDist: ExprDist := ExprDist.empty
    for (type, w) in typeDist.terms.toArray do
      if wb - w > 0 then
        let ic := c / (typesCum.findD w typesTop)
        let isleDist ←   isleM type evolve (wb -w -1) ic init d true false true  
        finalDist ←  finalDist ++ isleDist
    return finalDist

def weightByType(cost: Nat): ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, w) in init.terms.toArray do
    let α := ← whnf (← inferType x)
    match init.terms.find? α   with
    | some w  => finalDist ←  ExprDist.updateExprM finalDist x (w + cost)
    | _ => ()
  return finalDist

def refineWeight(weight? : Expr → TermElabM (Option Nat)):
      ExprDist → TermElabM ExprDist := fun init => do
  let mut finalDist := init
  for (x, w) in init.terms.toArray do
    match ← weight? x   with
    | some w  => finalDist ←  ExprDist.updateExprM finalDist x (w)
    | _ => ()
  return finalDist

def logResults(goals : Array Expr) : ExprDist →  TermElabM Unit := fun dist => do
    for g in goals do
      logInfo m!"goal: {g}"
      let statement ←  (dist.terms.findM? $ fun s => isDefEq s g)
      let statement ←  statement.mapM $ fun (e, w) => do (← whnf e, w) 
      if ← isType g then
        logInfo m!"statement generated: {← statement}"
        let proof ←  dist.terms.findM? $ fun t => do isDefEq (← inferType t) g
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
  let initData : FullData := (nameDist, [])
  let goals? ← goals?.mapM $ fun goals => parseExprList goals
  let goals := goals?.getD #[]
  let ev := ev.fixedPoint.evolve.andThenM (logResults goals)
  let wb ← parseNat wb
  let card ← parseNat card
  let finalDist ← ev wb card (← ExprDist.fromTerms initDist) initData
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