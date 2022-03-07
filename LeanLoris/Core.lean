import LeanLoris.FinDist
import LeanLoris.ExprDist
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

partial def exprNat : Expr → TermElabM Nat := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp := mkApp (mkConst ``Nat.succ) mvar
    if ← isDefEq sExp expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      let prev ← exprNat (← whnf mvar)
      return succ prev
    else 
    if ← isDefEq (mkConst `Nat.zero) expr then
      return zero
    else
      throwError m!"{expr} not a Nat expression"

-- #eval exprNat (ToExpr.toExpr 3)

def parseNat : Syntax → TermElabM Nat := fun s => 
  do
    let expr ← elabTerm s none
    exprNat expr



-- Basic functions for generation

-- (optional) function application with unification
def apply? (f x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x] none (explicit := false) (ellipsis := false)
      let exprType ← inferType expr
      if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  then 
        Term.synthesizeSyntheticMVarsNoPostponing
        return some <| ← whnf expr
      else return none
    catch e =>
      return none

def applyPair? (f x y : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x, Arg.expr y] none 
                    (explicit := false) (ellipsis := false)
      let exprType ← inferType expr
      if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  then 
        Term.synthesizeSyntheticMVarsNoPostponing
        return some <| ← whnf expr
      else return none
    catch e =>
      return none

def mkApp? (f x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr:= mkApp f x
      let exprType ← inferType expr
      if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  then 
        let expr ← whnf expr
        Term.synthesizeSyntheticMVarsNoPostponing
        return some expr
      else return none
    catch e =>
      return none

def mkAppPair? (f x y : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr:= mkAppN f #[x, y]
      let exprType ← inferType expr
      if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  then 
        Term.synthesizeSyntheticMVarsNoPostponing
        return some <| ← whnf expr
      else return none
    catch e =>
      return none

-- (optional) function application with unification given name of function
def nameApply? (f: Name) (x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x]
      let exprType ← inferType expr
      if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        Term.synthesizeSyntheticMVarsNoPostponing
        return some <| ← whnf expr
      else
      Elab.logWarning m!"not type correct : {expr} = {f} ({x})" 
      return none
    catch e =>
        -- Elab.logInfo m!"failed from name, arg : 
        --     {f} at {x} with type {← inferType x}"
      return none

-- (optional) function application with unification given name of function and a pair of arguments
def nameApplyPair? (f: Name) (x y: Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x, y]
      let exprType ← inferType expr
      if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        Term.synthesizeSyntheticMVarsNoPostponing
        return some <| ← whnf expr
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
    | none => return none
    | some (α , lhs, rhs) =>
    let heqType := if symm then ← mkEq rhs lhs else heqType
    let hep := if symm then mkEqSymm heq else return heq
    if lhs.getAppFn.isMVar then return none
    else
    let e ← instantiateMVars e
    let eAbst ←  kabstract e lhs
    if !eAbst.hasLooseBVars then return none
    else
    let eNew := eAbst.instantiate1 rhs
    let eNew ← instantiateMVars eNew
    let eEqE ← mkEq e e
    let eEqEAbst := mkApp eEqE.appFn! eAbst
    let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst
    if !(← isTypeCorrect motive) then return none
    else            
    let eqRefl ← mkEqRefl e
    let eqPrf ← mkEqNDRec motive eqRefl heq
    return some eqPrf

-- transports a term using equlity if its type can be rewritten
def rwPush?(symm : Bool)(e : Expr) (heq : Expr) : TermElabM (Option Expr) :=
  do
    let t ← inferType e
    let pf? ← rewriteProof t heq symm
    match pf? with
    | none => return none
    | some pf =>
      try
        let expr ← mkAppM ``Eq.mp #[pf, e]
        let exprType ← inferType expr
        if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  
        then 
        Term.synthesizeSyntheticMVarsNoPostponing
        return some <| ← whnf expr
        else return none
      catch _ => 
        return none

-- (optional) congrArg for an equality
def congrArg? (f: Expr)(eq : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM ``congrArg #[f, eq]
      let exprType ← inferType expr
      if ← (isTypeCorrect expr <&&>  isTypeCorrect exprType)  then 
      Term.synthesizeSyntheticMVarsNoPostponing
      return some <| ← whnf expr
      else 
        return none
    catch e => 
      return none 

-- return Boolean pair (is-new, not-external)
class NewElem (α D: Type) where
  newElem: D → α → Nat → TermElabM (Bool × Bool)

def newElem{α D : Type}[c: NewElem α D](d : D)(a : α)(n : Nat) : 
    TermElabM (Bool × Bool) := c.newElem d a n

def constNewElem{α D: Type}: Bool × Bool →  NewElem α D
  | ans => ⟨fun d a wb => pure ans⟩

-- generating distributions by combining


def prodGenArrM{α β D: Type}[NewElem α D][nb : NewElem β D][ToMessageData α][ToMessageData β]
    (compose: α → β → TermElabM (Option Expr))
    (maxWeight card: Nat)(fst: Array (α × Nat))(snd: Array (β × Nat))
    (data: D) : TermElabM ExprDist := do 
    -- logInfo m!"generating from pairs {← IO.monoMsNow}"
    if maxWeight > 0 then
      let mut fstTagGrouped: HashMap Nat (Array (α × Bool × Bool)) := HashMap.empty
      let mut sndTagGrouped: HashMap Nat (Array (β × Bool × Bool)) := HashMap.empty
      for (a, w1) in fst do
        let prev := fstTagGrouped.findD w1 #[]
        fstTagGrouped := fstTagGrouped.insert w1 <| prev.push (a, ← newElem data a w1)
      for (b, w2) in snd do
        let prev := sndTagGrouped.findD w2 #[]
        sndTagGrouped := sndTagGrouped.insert w2 <| prev.push (b, ← newElem data b w2)
      -- logInfo m!"finisher tagging whether new {← IO.monoMsNow}"
      let fstAbove := weightAbove fst maxWeight
      let sndAbove := weightAbove snd maxWeight
      let mut wtdPairs : Array (α × β  × Nat) := #[]
      for w1 in [0:maxWeight] do
        for w2 in [0:maxWeight-w1] do
          if (fstAbove.findD w1 0) * (sndAbove.findD w2 0) ≤ card
          then 
            for (e1, b1, be1) in fstTagGrouped.findD w1 #[] do 
              for (e2, b2, be2) in sndTagGrouped.findD w2 #[] do 
                  if (((b1 || b2))
                    || ((be1 || be2) && w1 + w2  + 1 = maxWeight)) 
                  then
                    wtdPairs := wtdPairs.push (e1, e2, w1 + w2  + 1)
      -- logInfo m!"obtained weighted pairs {← IO.monoMsNow}"
      let arr1 : Array (TermElabM (Option (Expr × Nat))) := 
          wtdPairs.map <| fun (e1, e2, w) => 
                (compose e1 e2).map (fun oe => 
                      oe.map (fun e4 => (e4, w) ))
      let arr2 ←  arr1.filterMapM <| fun t => t
      -- logInfo m!"obtained resulting compositions {← IO.monoMsNow}; size: {arr2.size}"
      let res ← ExprDist.fromArrayM arr2 
      -- logInfo m!"obtained merged result {← IO.monoMsNow}; size : {res.termsArray.size} + {res.proofsArray.size}"
      return res
    else return ExprDist.empty

def prodPolyGenArrM{α β D: Type}[NewElem α D][nb : NewElem β D][ToMessageData α][ToMessageData β]
    (compose: α → β → TermElabM (Option (Array Expr)))
    (maxWeight card: Nat)(fst: Array (α × Nat))(snd: Array (β × Nat))
    (data: D) : TermElabM ExprDist := do 
    -- logInfo m!"generating from pairs {← IO.monoMsNow}"
    if maxWeight > 0 then
      let mut fstTagGrouped: HashMap Nat (Array (α × Bool × Bool)) := HashMap.empty
      let mut sndTagGrouped: HashMap Nat (Array (β × Bool × Bool)) := HashMap.empty
      for (a, w1) in fst do
        let prev := fstTagGrouped.findD w1 #[]
        fstTagGrouped := fstTagGrouped.insert w1 <| prev.push (a, ← newElem data a w1)
      for (b, w2) in snd do
        let prev := sndTagGrouped.findD w2 #[]
        sndTagGrouped := sndTagGrouped.insert w2 <| prev.push (b, ← newElem data b w2)
      -- logInfo m!"finisher tagging whether new {← IO.monoMsNow}"
      let fstAbove := weightAbove fst maxWeight
      let sndAbove := weightAbove snd maxWeight
      let mut wtdPairs : Array (α × β  × Nat) := #[]
      for w1 in [0:maxWeight] do
        for w2 in [0:maxWeight-w1] do
          if (fstAbove.findD w1 0) * (sndAbove.findD w2 0) ≤ card
          then 
            for (e1, b1, be1) in fstTagGrouped.findD w1 #[] do 
              for (e2, b2, be2) in sndTagGrouped.findD w2 #[] do 
                  if (((b1 || b2))
                    || ((be1 || be2) && w1 + w2  + 1 = maxWeight)) 
                  then
                    wtdPairs := wtdPairs.push (e1, e2, w1 + w2  + 1)
      -- logInfo m!"obtained weighted pairs {← IO.monoMsNow}"
      let mut arr1 : Array (Option (Expr × Nat)) := #[]
      for (e1, e2, w) in wtdPairs do 
        match ← compose e1 e2 with
        | none => pure ()
        | some a => 
          for e3 in a do 
            arr1 := arr1.push (some (e3, w))        
      let arr2 :=  arr1.filterMap <| fun t => t
      -- logInfo m!"obtained resulting compositions {← IO.monoMsNow}; size: {arr2.size}"
      let res ← ExprDist.fromArrayM arr2 
      -- logInfo m!"obtained merged result {← IO.monoMsNow}; size : {res.termsArray.size} + {res.proofsArray.size}"
      return res
    else return ExprDist.empty

def tripleProdGenArrM{α β γ  D: Type}[NewElem α D][NewElem β D][NewElem γ D]
    (compose: α → β → γ → TermElabM (Option Expr))
    (maxWeight card: Nat)(fst: Array (α × Nat))(snd: Array (β × Nat))
    (third : Array (γ × Nat))(data: D) : TermElabM ExprDist := do 
    -- logInfo m!"generating from triples {← IO.monoMsNow}"
    if maxWeight > 0 then
      let mut fstTagGrouped: HashMap Nat (Array (α × Bool × Bool)) := HashMap.empty
      let mut sndTagGrouped: HashMap Nat (Array (β × Bool × Bool)) := HashMap.empty
      let mut thirdTagGrouped: HashMap Nat (Array (γ × Bool × Bool)) := HashMap.empty
      for (a, w1) in fst do
        let prev := fstTagGrouped.findD w1 #[]
        fstTagGrouped := fstTagGrouped.insert w1 <| prev.push (a, ← newElem data a w1)
      for (b, w2) in snd do
        let prev := sndTagGrouped.findD w2 #[]
        sndTagGrouped := sndTagGrouped.insert w2 <| prev.push (b, ← newElem data b w2)
      for (c, w3) in third do
        let prev := thirdTagGrouped.findD w3 #[]
        thirdTagGrouped := thirdTagGrouped.insert w3 <| prev.push (c, ← newElem data c w3) 
      -- logInfo m!"finisher tagging whether new {← IO.monoMsNow}"
      let fstAbove := weightAbove fst maxWeight
      let sndAbove := weightAbove snd maxWeight
      let thirdAbove := weightAbove third maxWeight    
      let mut wtdTriples : Array (α × β × γ  × Nat) := #[]
      for w1 in [0:maxWeight] do
        for w2 in [0:maxWeight-w1] do
          for w3 in [0:maxWeight-w1-w2] do
          if (fstAbove.findD w1 0) * (sndAbove.findD w2 0) * (thirdAbove.findD w3 0) ≤ card
          then 
            for (e1, b1, be1) in fstTagGrouped.findD w1 #[] do 
              for (e2, b2, be2) in sndTagGrouped.findD w2 #[] do 
                for (e3, b3, be3) in thirdTagGrouped.findD w3 #[] do 
                  if (((b1 || b2 || b3))
                    || ((be1 || be2 || be3) && w1 + w2 + w3 + 1 = maxWeight)) 
                  then
                    wtdTriples := wtdTriples.push (e1, e2, e3, w1 + w2 + w3 + 1)
      -- logInfo m!"obtained weighted triples {← IO.monoMsNow}; size : {wtdTriples.size}"
      let arr1 : Array (TermElabM (Option (Expr × Nat))) := 
          wtdTriples.map <| fun (e1, e2, e3, w) => 
                (compose e1 e2 e3).map (fun oe => 
                      oe.map (fun e4 => (e4, w) ))
      let arr2 ←  arr1.filterMapM <| fun t => t
      -- logInfo m!"obtained resulting compositions {← IO.monoMsNow}; size: {arr2.size}"
      let res ← ExprDist.fromArrayM arr2
      -- logInfo m!"obtained merged result {← IO.monoMsNow}; size : {res.termsArray.size} + {res.proofsArray.size}"
      return res
    else return ExprDist.empty

-- Deprecated

def prodGenM{α β : Type}[Hashable α][BEq α][Hashable β][BEq β]
    (compose: α → β → TermElabM (Option Expr))
    (maxWeight card: Nat)(fst: FinDist α)(snd: FinDist β)
    (newPair: Nat → Nat →  α × β → Nat × Nat → TermElabM Bool) : TermElabM ExprDist := do 
    let mut w := ExprDist.empty
    if maxWeight > 0 then
      let fstBdd := fst.bound (maxWeight - 1) card
      let fstCount := fstBdd.cumulWeightCount maxWeight
      for (key, val) in fstBdd.toArray do
      if maxWeight - val > 0 then
        let fstNum := fstCount.find! val 
        let sndCard := card / fstNum
        let sndBdd := snd.bound (maxWeight - val - 1) sndCard
        for (key2, val2) in sndBdd.toArray do
          if ←  newPair maxWeight card (key, key2) (val, val2) then
            match ← compose key key2 with
            | some key3 =>
                w ←  ExprDist.updateExprM w key3 (val + val2 + 1)
            | none => pure ()
          -- else logWarning m!"newPair failed {val} {val2} ; {maxWeight}"
    return w

def tripleProdGenM{α β γ : Type}[Hashable α][BEq α][Hashable β][BEq β]
    [Hashable γ][BEq γ]
    (compose: α → β → γ  →  TermElabM (Option Expr))
    (maxWeight card: Nat)
    (fst: FinDist α)(snd: FinDist β)(third : FinDist γ)
    (newTriple: Nat → Nat →  α × β × γ → Nat × Nat × Nat → TermElabM Bool) : TermElabM ExprDist := do 
    let mut w := ExprDist.empty
    if maxWeight > 0 then
      let fstBdd := fst.bound (maxWeight - 1) card
      let fstCount := fstBdd.cumulWeightCount maxWeight
      let fstTop := (fstCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
      for (key, val) in fstBdd.toArray do
      if maxWeight - val > 0 then
        let fstNum := fstCount.findD val 0
        let sndCard := card / fstNum
        let sndBdd := snd.bound (maxWeight - val - 1) sndCard
        let sndCount := sndBdd.cumulWeightCount maxWeight
        let sndTop := (sndCount.toList.map (fun (k, v) => v)).maximum?.getD 1 
        for (key2, val2) in sndBdd.toArray do
        if maxWeight - val - val2 > 0 then
          let sndNum := sndCount.findD val2 0
          let thirdCard := sndCard / sndNum
          let thirdBdd := third.bound (maxWeight - val - val2 - 1) thirdCard
          for (key3, val3) in thirdBdd.toArray do
            if ←  newTriple maxWeight card (key, key2, key3) (val, val2, val3) then
              match ← compose key key2 key3 with
              | some key3 =>
                  w ←  ExprDist.updateExprM w key3 (val + val2 + val3 + 1)
              | none => pure ()
    return w

