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

/- 
  Hashmaps for distributions; especially for expressions; with basic map, filter methods
  including Mondaic forms
-/
abbrev FinDist (α : Type)[Hashable α][BEq α] := HashMap α Nat 

abbrev ExprDist := FinDist Expr 

abbrev NameDist := FinDist Name

namespace FinDist

def empty{α : Type} [Hashable α][BEq α] : FinDist α := HashMap.empty

def fromList{α : Type}[Hashable α][BEq α] (l : List (α  × Nat)) : FinDist α :=
  l.foldl (fun m (a, n) => m.insert a n) HashMap.empty

def merge{α : Type}[Hashable α][BEq α] 
    (fst: FinDist α)(snd: FinDist α) : FinDist α  := Id.run do
  let mut min := fst
  for (key, val) in snd.toArray do
    match min.find? key with
    | some v =>
      if val < v then
        min := min.insert key val
    | none => 
        min := min.insert key val
  return min

instance {α : Type}[Hashable α][BEq α ]: Append <| FinDist α  := 
                                  ⟨fun fst snd => fst.merge snd⟩


def map{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (dist: FinDist α)(f: α → β ) : FinDist β   := 
  dist.toArray.foldl (fun map (key, val) => 
    let y : β  :=  f key
    match map.find? <| y with
    | some v =>
      map.insert y (min v val)
    | none => 
      map.insert y val
    ) FinDist.empty

def mapM{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (dist: FinDist α)(f: α → TermElabM β ) : TermElabM <| FinDist β  := 
  dist.toArray.foldlM (fun map (key, val) => do
    let y : β  ←  f key
    match map.find? <| y with
    | some v =>
      map.insert y (min v val)
    | none => 
      map.insert y val
    ) FinDist.empty

def weightCount{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) : HashMap Nat Nat := 
      m.toArray.foldl (fun w (key, val) =>
        match w.find? val with
        | some v =>
          w.insert val (v + 1)
        | none => 
          w.insert val 1
      ) HashMap.empty

def cumulWeightCount{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) : HashMap Nat Nat := Id.run do
      let base := weightCount m
      let maxWeight := base.toList.foldl (fun max (key, val) =>
        if key > max then
          key
        else
          max
      ) 0
      let mut w := HashMap.empty
      for (key, val) in base.toArray do
        for j in [key: (maxWeight + 1)] do
          match w.find? j with
          | some v =>
            w := w.insert j (v + val)
          | none => 
            w := w.insert j val
      return w

def filter{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (p: α → Bool) : FinDist α := 
  m.toArray.foldl (fun w (key, val) => 
    if p key then
      w.insert key val
    else w
  ) FinDist.empty

def filterM{α : Type}[Hashable α][BEq α]
    (m: FinDist α ) (p: α  → TermElabM Bool) : TermElabM <| FinDist α := do
  m.toArray.foldlM (fun w (key, val) => do 
    if ←  p key then
      w.insert key val
    else w
  ) FinDist.empty

def bound{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (maxWeight card: Nat)  : FinDist α := Id.run do
  let mut w := FinDist.empty
  let cumul := cumulWeightCount m
  let top := (cumul.toList.map (fun (k, v) => v)).maximum?.getD 1 
  for (key, val) in m.toArray do
    if val ≤ maxWeight && (cumul.findD val top ≤ card) then
      w := w.insert key val
  return w

def zeroLevel{α : Type}[Hashable α][BEq α] 
    (arr: Array α) : FinDist α := Id.run do
  arr.foldl (fun w x => w.insert x 0) FinDist.empty

def update{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (x: α) (d: Nat) : FinDist α := 
  match m.find? x with
  | some v => if d < v then m.insert x d else m
  | none => m.insert x d

def keys{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) := m.toList.map (fun (k, v) => k)

def findM?{α : Type}[Hashable α][BEq α] 
    (m: FinDist α)(p: α → TermElabM Bool) : TermElabM (Option α) := 
      m.keys.findM? p

end FinDist


def FinDist.exists{α : Type}[Hashable α][BEq α] 
    (m: FinDist α) (elem: α)(weight: Nat) : Bool :=
    match m.find? elem with
    | some v => v ≤ weight
    | none => false


def prodGen{α β γ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ](fst: FinDist α)(snd: FinDist β)
    (maxWeight card: Nat)(compose: α → β → Option γ)
    (newPair: α × β → Bool) : FinDist γ  := Id.run do 
    let mut w : FinDist γ := FinDist.empty
    if maxWeight > 0 then
      let fstBdd := fst.bound (maxWeight - 1) card
      let fstCount := fstBdd.cumulWeightCount
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
      for (key, val) in fstBdd.toArray do
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := snd.bound (maxWeight - val - 1) sndCard
        for (key2, val2) in sndBdd.toArray do
          if newPair (key, key2) then
            match compose key key2 with
            | some key3 =>
                w := w.update key3 (val + val2 + 1)
            | none => ()
    return w

def prodGenM{α β γ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ](compose: α → β → TermElabM (Option γ))
    (maxWeight card: Nat)(fst: FinDist α)(snd: FinDist β)
    (newPair: Nat → Nat →  α × β → Nat × Nat → Bool) : TermElabM (FinDist γ) := do 
    let mut w := FinDist.empty
    if maxWeight > 0 then
      let fstBdd := fst.bound (maxWeight - 1) card
      let fstCount := fstBdd.cumulWeightCount
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
      for (key, val) in fstBdd.toArray do
      if maxWeight - val > 0 then
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := snd.bound (maxWeight - val - 1) sndCard
        for (key2, val2) in sndBdd.toArray do
          if newPair maxWeight card (key, key2) (val, val2) then
            match ← compose key key2 with
            | some key3 =>
                w := FinDist.update w key3 (val + val2 + 1)
            | none => ()
    return w

def tripleProdGen{α β γ δ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ][Hashable δ][BEq δ](compose: α → β → γ  → Option δ)
    (maxWeight card: Nat)
    (fst: FinDist α)(snd: FinDist β)(third : FinDist γ)
    (newTriple: Nat → Nat →  α × β × γ → Nat × Nat × Nat  → Bool) : FinDist δ := Id.run do 
    let mut w := FinDist.empty
    if maxWeight > 0 then
      let fstBdd := fst.bound (maxWeight - 1) card
      let fstCount := fstBdd.cumulWeightCount
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
      for (key, val) in fstBdd.toArray do
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := snd.bound (maxWeight - val - 1) sndCard
        let sndCount := sndBdd.cumulWeightCount
        let sndTop := (sndCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
        for (key2, val2) in sndBdd.toArray do
          let sndNum := sndCount.findD val2 sndTop
          let thirdCard := sndCard / sndNum
          let thirdBdd := third.bound (maxWeight - val - val2 - 1) thirdCard
          for (key3, val3) in thirdBdd.toArray do
            if newTriple maxWeight card (key, key2, key3) (val, val2, val3) then
              match compose key key2 key3 with
              | some key3 =>
                  w := FinDist.update w key3 (val + val2 + val3 + 1)
              | none => ()
    return w

def tripleProdGenM{α β γ δ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ][Hashable δ][BEq δ]
    (compose: α → β → γ  → TermElabM (Option δ))
    (maxWeight card: Nat)
    (fst: FinDist α)(snd: FinDist β)(third : FinDist γ)
    (newTriple: Nat → Nat →  α × β × γ → Nat × Nat × Nat → Bool) : TermElabM <| FinDist δ := do 
    let mut w := FinDist.empty
    if maxWeight > 0 then
      let fstBdd := fst.bound (maxWeight - 1) card
      let fstCount := fstBdd.cumulWeightCount
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
      for (key, val) in fstBdd.toArray do
      if maxWeight - val > 0 then
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := snd.bound (maxWeight - val - 1) sndCard
        let sndCount := sndBdd.cumulWeightCount
        let sndTop := (sndCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
        for (key2, val2) in sndBdd.toArray do
        if maxWeight - val - val2 > 0 then
          let sndNum := sndCount.findD val2 sndTop
          let thirdCard := sndCard / sndNum
          let thirdBdd := third.bound (maxWeight - val - val2 - 1) thirdCard
          for (key3, val3) in thirdBdd.toArray do
            if newTriple maxWeight card (key, key2, key3) (val, val2, val3) then
              match ← compose key key2 key3 with
              | some key3 =>
                  w := FinDist.update w key3 (val + val2 + val3 + 1)
              | none => ()
    return w

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

def andThenM{D: Type} (recEv : RecEvolverM D) (f: ExprDist → ExprDist) : RecEvolverM D := 
      fun wb cb initDist data evo => 
        do
          let newDist ← recEv wb cb initDist data evo
          f newDist

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

-- Auxiliary functions mainly from lean source for finding subexpressions

def isBlackListed  (declName : Name) : TermElabM  Bool := do
  let env ← getEnv
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRecCore env declName
  <||> isMatcherCore env declName

def isAux (declName : Name) : TermElabM  Bool := do
  let env ← getEnv
  isAuxRecursor env declName
  <||> isNoConfusion env declName
  
def isNotAux  (declName : Name) : TermElabM  Bool := do
  let nAux ← isAux declName
  return (not nAux)

def isWhiteListed (declName : Name) : TermElabM Bool := do
  let bl ← isBlackListed  declName
  return !bl


-- Basic functions for generation

-- (optional) function application with unification
def applyOpt (f x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x] none (explicit := false) (ellipsis := false)
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then 
        return some <| ← whnf expr
      else return none
    catch e =>
      return none

-- (optional) function application with unification given name of function
def nameApplyOpt (f: Name) (x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        return some expr
      else
      Elab.logWarning m!"not type correct : {expr} = {f} ({x})" 
      return none
    catch e =>
        -- Elab.logInfo m!"failed from name, arg : 
        --     {f} at {x} with type {← inferType x}"
      return none

-- (optional) function application with unification given name of function and a pair of arguments
def nameApplyPairOpt (f: Name) (x y: Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x, y]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        return some expr
      else
      Elab.logWarning m!"not type correct : {expr} = {f}({x}, {y})" 
      return none
    catch e =>
        -- Elab.logInfo m!"failed from name, arg : 
        --     {f} at {x}, {y} with type {← inferType x}"
      return none


-- copied from lean4 source code and modified; optionally returns proof that
-- a rewritten expression is equal to the original one.
def rewriteProof (e: Expr) (heq : Expr) (symm : Bool := false) : MetaM (Option Expr) :=
  do
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    match heqType.eq? with
    | none => none
    | some (α , lhs, rhs) =>
    let heqType := if symm then ← mkEq rhs lhs else heqType
    let hep := if symm then mkEqSymm heq else heq
    if lhs.getAppFn.isMVar then none
    else
    let e ← instantiateMVars e
    let eAbst ←  kabstract e lhs
    if !eAbst.hasLooseBVars then none
    else
    let eNew := eAbst.instantiate1 rhs
    let eNew ← instantiateMVars eNew
    let eEqE ← mkEq e e
    let eEqEAbst := mkApp eEqE.appFn! eAbst
    let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst
    if !(← isTypeCorrect motive) then none
    else            
    let eqRefl ← mkEqRefl e
    let eqPrf ← mkEqNDRec motive eqRefl heq
    return some eqPrf

-- transports a term using equlity if its type can be rewritten
def rwPushOpt(symm : Bool)(e : Expr) (heq : Expr) : TermElabM (Option Expr) :=
  do
    let t ← inferType e
    let pfOpt ← rewriteProof t heq symm
    match pfOpt with
    | none => return none
    | some pf =>
      try
        let expr ← mkAppM ``Eq.mp #[pf, e]
        let exprType ← inferType expr
        if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  
        then return some expr
        else return none
      catch _ => 
        return none

-- (optional) congrArg for an equality
def congrArgOpt (f: Expr)(eq : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM ``congrArg #[f, eq]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then return some expr
      else 
        return none
    catch e => 
      return none 

-- Some evolution cases; just one step (so update not needed)

def applyEvolver(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let funcs ← init.filterM $ fun e => 
       do Expr.isForall <| ← inferType e
    prodGenM applyOpt wb c funcs init (isNewPair d)

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

def egEvolver : EvolutionM Unit := 
  ((applyEvolver Unit).tautRec ++ (RecEvolverM.init Unit)).fixedPoint

