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

abbrev ExprDist := HashMap Expr Nat

def mapFromList{α : Type}[Hashable α][BEq α] (l : List (α  × Nat)) : HashMap α Nat :=
  l.foldl (fun m (a, n) => m.insert a n) HashMap.empty

def mergeDist{α : Type}[Hashable α][BEq α] 
    (fst: HashMap α Nat)(snd: HashMap α Nat)  := Id.run do
  let mut min := fst
  for (key, val) in snd.toArray do
    match min.find? key with
    | some v =>
      if val < v then
        min := min.insert key val
    | none => 
        min := min.insert key val
  return min

def mapDist{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (dist: HashMap α Nat)(f: α → β )  := 
  dist.toArray.foldl (fun map (key, val) => 
    let y : β  :=  f key
    match map.find? <| y with
    | some v =>
      map.insert y (min v val)
    | none => 
      map.insert y val
    ) HashMap.empty

def mapDistM{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (dist: HashMap α Nat)(f: α → TermElabM β ) : TermElabM <| HashMap β Nat  := 
  dist.toArray.foldlM (fun map (key, val) => do
    let y : β  ←  f key
    match map.find? <| y with
    | some v =>
      map.insert y (min v val)
    | none => 
      map.insert y val
    ) HashMap.empty

def weightCount{α : Type}[Hashable α][BEq α] 
    (m: HashMap α Nat) : HashMap Nat Nat := 
      m.toArray.foldl (fun w (key, val) =>
        match w.find? val with
        | some v =>
          w.insert val (v + 1)
        | none => 
          w.insert val 1
      ) HashMap.empty

def cumulWeightCount{α : Type}[Hashable α][BEq α] 
    (m: HashMap α  Nat) : HashMap Nat Nat := Id.run do
      let base := weightCount m
      let mut w := base
      for (key, val) in base.toArray do
        for j in [0:key] do
          match w.find? j with
          | some v =>
            w := w.insert j (v + val)
          | none => 
            w := w.insert j val
      return w

def filterDist{α : Type}[Hashable α][BEq α] 
    (m: HashMap α Nat) (p: α → Bool) : HashMap α Nat := 
  m.toArray.foldl (fun w (key, val) => 
    if p key then
      w.insert key val
    else w
  ) HashMap.empty

def filterDistM{α : Type}[Hashable α][BEq α]
    (m: HashMap α Nat) (p: α  → TermElabM Bool) : TermElabM <| HashMap α Nat := do
  m.toArray.foldlM (fun w (key, val) => do 
    if ←  p key then
      w.insert key val
    else w
  ) HashMap.empty

def boundDist{α : Type}[Hashable α][BEq α] 
    (m: HashMap α Nat) (maxWeight card: Nat)  : HashMap α Nat := Id.run do
  let mut w := HashMap.empty
  let cumul := cumulWeightCount m
  let top := (cumul.toList.map (fun (k, v) => v)).maximum?.getD 0 
  for (key, val) in m.toArray do
    if val ≤ maxWeight && (cumul.findD val top ≤ card) then
      w := w.insert key val
  return w

def inDist{α : Type}[Hashable α][BEq α] 
    (m: HashMap α Nat) (elem: α)(weight: Nat) : Bool :=
    match m.find? elem with
    | some v => v ≤ weight
    | none => false

def zeroLevelDist{α : Type}[Hashable α][BEq α] 
    (arr: Array α) : HashMap α Nat := Id.run do
  arr.foldl (fun w x => w.insert x 0) HashMap.empty

def distUpdate{α : Type}[Hashable α][BEq α] 
    (m: HashMap α Nat) (x: α) (d: Nat) : HashMap α Nat := 
  match m.find? x with
  | some v => if d < v then m.insert x d else m
  | none => m.insert x d

def prodGen{α β γ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ](fst: HashMap α Nat)(snd: HashMap β Nat)
    (maxWeight card: Nat)(compose: α → β → Option γ)
    (newPair: α × β → Bool) : HashMap γ  Nat := Id.run do 
    let mut w := HashMap.empty
    if maxWeight > 0 then
      let fstBdd := boundDist fst (maxWeight - 1) card
      let fstCount := cumulWeightCount fstBdd
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 0 
      for (key, val) in fstBdd.toArray do
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := boundDist snd (maxWeight - val - 1) sndCard
        for (key2, val2) in sndBdd.toArray do
          if newPair (key, key2) then
            match compose key key2 with
            | some key3 =>
                w := distUpdate w key3 (val + val2 + 1)
            | none => ()
    return w

def prodGenM{α β γ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ](compose: α → β → TermElabM (Option γ))
    (maxWeight card: Nat)(fst: HashMap α Nat)(snd: HashMap β Nat)
    (newPair: Nat → Nat →  α × β → Nat × Nat → Bool) : TermElabM (HashMap γ  Nat) := do 
    let mut w := HashMap.empty
    if maxWeight > 0 then
      let fstBdd := boundDist fst (maxWeight - 1) card
      let fstCount := cumulWeightCount fstBdd
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 0 
      for (key, val) in fstBdd.toArray do
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := boundDist snd (maxWeight - val - 1) sndCard
        for (key2, val2) in sndBdd.toArray do
          if newPair maxWeight card (key, key2) (val, val2) then
            match ← compose key key2 with
            | some key3 =>
                w := distUpdate w key3 (val + val2 + 1)
            | none => ()
    return w

def tripleProdGen{α β γ δ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ][Hashable δ][BEq δ](compose: α → β → γ  → Option δ)
    (maxWeight card: Nat)
    (fst: HashMap α Nat)(snd: HashMap β Nat)(third : HashMap γ Nat)
    (newTriple: Nat → Nat →  α × β × γ  → Bool) : HashMap δ Nat := Id.run do 
    let mut w := HashMap.empty
    if maxWeight > 0 then
      let fstBdd := boundDist fst (maxWeight - 1) card
      let fstCount := cumulWeightCount fstBdd
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 0 
      for (key, val) in fstBdd.toArray do
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := boundDist snd (maxWeight - val - 1) sndCard
        let sndCount := cumulWeightCount sndBdd
        let sndTop := (sndCount.toList.map (fun (k, v) => v)).maximum?.getD 0 
        for (key2, val2) in sndBdd.toArray do
          let sndNum := sndCount.findD val2 sndTop
          let thirdCard := sndCard / sndNum
          let thirdBdd := boundDist third (maxWeight - val - val2 - 1) thirdCard
          for (key3, val3) in thirdBdd.toArray do
            if newTriple maxWeight card (key, key2, key3) then
              match compose key key2 key3 with
              | some key3 =>
                  w := distUpdate w key3 (val + val2 + val3 + 1)
              | none => ()
    return w

def tripleProdGenM{α β γ δ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ][Hashable δ][BEq δ]
    (fst: HashMap α Nat)(snd: HashMap β Nat)(third : HashMap γ Nat)
    (maxWeight card: Nat)(compose: α → β → γ  → TermElabM (Option δ))
    (newPair: α × β × γ  → Bool) : TermElabM <| HashMap δ Nat := do 
    let mut w := HashMap.empty
    if maxWeight > 0 then
      let fstBdd := boundDist fst (maxWeight - 1) card
      let fstCount := cumulWeightCount fstBdd
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 0 
      for (key, val) in fstBdd.toArray do
        let fstNum := fstCount.findD val fstTop
        let sndCard := card / fstNum
        let sndBdd := boundDist snd (maxWeight - val - 1) sndCard
        let sndCount := cumulWeightCount sndBdd
        let sndTop := (sndCount.toList.map (fun (k, v) => v)).maximum?.getD 0 
        for (key2, val2) in sndBdd.toArray do
          let sndNum := sndCount.findD val2 sndTop
          let thirdCard := sndCard / sndNum
          let thirdBdd := boundDist third (maxWeight - val - val2 - 1) thirdCard
          for (key3, val3) in thirdBdd.toArray do
            if newPair (key, key2, key3) then
              match ← compose key key2 key3 with
              | some key3 =>
                  w := distUpdate w key3 (val + val2 + val3 + 1)
              | none => ()
    return w

structure GenDist where
  weight: Nat
  card : Nat
  exprDist : ExprDist

class DataUpdate (D: Type) where
  update: ExprDist → D → D

def dataUpdate{D: Type}[du : DataUpdate D](d: ExprDist) : D → D :=
  du.update d

def idUpate{D: Type} : DataUpdate D :=
  ⟨fun _ d => d⟩

instance : DataUpdate Unit := idUpate 

class IsNew (D: Type) where
  isNew: D → Nat → Nat →  Expr → Nat →  Bool

def isNew{D: Type}[c: IsNew D] : D → Nat → Nat →   Expr  → Nat  → Bool :=
  c.isNew

def allNew{D: Type} : IsNew D :=
  ⟨fun d _ _ e _ => true⟩

instance : IsNew Unit := allNew

def newPair?{D: Type}[c: IsNew D] : D → Nat → Nat →  (Expr ×   Expr) → (Nat × Nat)  → Bool :=
  fun d wb cb (e1, e2) (w1, w2) => isNew d wb cb e1 w1 || isNew d wb cb e2 w2

class NameDist (D: Type) where
  nameDist: D → HashMap Name Nat

def nameDist{D: Type}[c: NameDist D] : D  → HashMap Name Nat :=
  c.nameDist

class DistHist (D: Type) where
  distHist: D → List GenDist

def newFromHistory {D: Type}[cl: DistHist D] : IsNew D :=
  ⟨fun d wb c e w =>
    let hist := (cl.distHist d).filter <| fun gd => wb ≤ gd.weight  && c ≤  gd.card  
    hist.any <| fun dist =>  inDist dist.exprDist e w⟩

instance {D: Type}[cl: DistHist D] : IsNew D := newFromHistory 

-- same signature for full evolution and single step, with ExprDist being initial state or accumulated state and the wieght bound that for the result or the accumulated state
def Evolution(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist  → (initData: D) → ExprDist

def initEvolution(D: Type) : Evolution D := fun _ _ init _ => init

-- can again play two roles; and is allowed to depend on a generator; diagonal should only be used for full generation, not for single step.
def RecEvolver(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist → (initData: D) → (evo: Evolution D) → ExprDist

instance{D: Type} : Inhabited <| Evolution D := ⟨initEvolution D⟩

partial def RecEvolver.diag{D: Type}(recEv: RecEvolver D) : Evolution D :=
        fun d c init memo => recEv d c init  memo (diag recEv)

-- same signature for full evolution and single step, with ExprDist being initial state or accumulated state and the wieght bound that for the result or the accumulated state
def EvolutionM(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist  → (initData: D) → TermElabM ExprDist


-- can again play two roles; and is allowed to depend on a generator; diagonal should only be used for full generation, not for single step.
def RecEvolverM(D: Type) : Type := (weightBound: Nat) → (cardBound: Nat) →  ExprDist → (initData: D) → (evo: EvolutionM D) → TermElabM ExprDist

namespace EvolutionM

def init(D: Type) : EvolutionM D := fun _ _ init _ => pure init

def tautRec{D: Type}(ev: EvolutionM D) : RecEvolverM D := 
        fun wb cb init d _ => ev wb cb init d

end EvolutionM


instance{D: Type} : Inhabited <| EvolutionM D := ⟨EvolutionM.init D⟩

namespace RecEvolverM

def init(D: Type) := (EvolutionM.init D).tautRec

partial def diag{D: Type}(recEv: RecEvolverM D) : EvolutionM D :=
        fun d c init memo => recEv d c init memo (diag recEv)

def iterateAux{D: Type}[DataUpdate D](stepEv : RecEvolverM D)(incWt accumWt cardBound: Nat) : 
                     ExprDist → (initData: D) → (evo: EvolutionM D) → TermElabM ExprDist := 
                     match incWt with
                     | 0 => fun initDist _ _ => return initDist
                     | m + 1 => fun initDist d evo => 
                      do
                        let newDist ←  stepEv (accumWt + 1) cardBound initDist d evo
                        let newData := dataUpdate newDist d
                        iterateAux stepEv m (accumWt + 1) cardBound newDist newData evo

def iterate{D: Type}[DataUpdate D](stepEv : RecEvolverM D): RecEvolverM D := 
      fun wb cb initDist data evo => 
        iterateAux stepEv wb 0 cb initDist data evo

def merge{D: Type}(fst: RecEvolverM D)(snd: RecEvolverM D) : RecEvolverM D := 
      fun wb cb initDist data evo => 
        do
          let fstDist ← fst wb cb initDist data evo
          let sndDist ← snd wb cb initDist data evo
          return mergeDist fstDist sndDist

end RecEvolverM

instance {D: Type}: Append <| RecEvolverM D := ⟨fun fst snd => fst.merge snd⟩

def EvolutionM.evolve{D: Type}[DataUpdate D](ev: EvolutionM D) : EvolutionM D :=
        ev.tautRec.iterate.diag

def isleM {D: Type}(type: Expr)(recEv : RecEvolverM D)(weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D)(evolve : EvolutionM D)(includePi : Bool := true)(excludeProofs: Bool := false): TermElabM (ExprDist) := 
    withLocalDecl Name.anonymous BinderInfo.default (type)  $ fun x => 
        do
          let dist := init.insert x 0
          -- logInfo m!"initial in isle: {l}"
          let evb ← recEv weightBound cardBound dist initData evolve
          let mut evl : ExprDist := HashMap.empty
          for (y, w) in evb.toArray do
            unless excludeProofs && ((← inferType y).isProp) do
              evl := distUpdate evl y w
          let evt ← filterDistM evl (fun x => liftMetaM (isType x))
          let exported ← mapDistM evl (fun e => mkLambdaFVars #[x] e)
          let exportedPi ← mapDistM evt (fun e => mkForallFVars #[x] e)
          let res := if includePi then mergeDist exported  exportedPi else exported
          return res

-- Auxiliary functions mainly from lean source for subexpressions

def isBlackListed (env: Environment) (declName : Name) : IO  Bool := do
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRecCore env declName
  <||> isMatcherCore env declName

def isAux (env: Environment) (declName : Name) : IO  Bool := do
  isAuxRecursor env declName
  <||> isNoConfusion env declName
  
def isNotAux (env: Environment) (declName : Name) : IO  Bool := do
  let nAux ← isAux env declName
  return (not nAux)

def isWhiteListed (env: Environment)(declName : Name) : IO Bool := do
  let bl ← isBlackListed env declName
  return !bl

def whiteListed (n: Name) : TermElabM Bool := do
  let b ← isWhiteListed (← getEnv) n
  return b

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
def eqCongrOpt (f: Expr)(eq : Expr) : TermElabM (Option Expr) :=
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
    let funcs ←   filterDistM init $ fun e => 
       do Expr.isForall <| ← inferType e
    prodGenM applyOpt wb c funcs init (newPair? d)

def nameApplyEvolver(D: Type)[IsNew D][NameDist D]: EvolutionM D := fun wb c init d =>
  do
    let names := nameDist d
    prodGenM nameApplyOpt wb c names init (
          fun wb c (_, e) (_, we) => 
            isNew d wb c e we)

def rewriteEvolver(flip: Bool)(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let eqls ←   filterDistM init $ fun e => 
       do Expr.isEq <| ← inferType e
    prodGenM (rwPushOpt flip) wb c init eqls (newPair? d)

def congrEvolver(D: Type)[IsNew D] : EvolutionM D := fun wb c init d => 
  do
    let funcs ←   filterDistM init $ fun e => 
       do Expr.isForall <| ← inferType e
    let eqls ←   filterDistM init $ fun e => 
       do Expr.isEq <| ← inferType e
    prodGenM eqCongrOpt wb c funcs eqls (newPair? d)

def egEvolver : EvolutionM Unit := 
  ((applyEvolver Unit).tautRec ++ (RecEvolverM.init Unit)).diag

