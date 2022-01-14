import LeanLoris.FinDist
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

def applyPairOpt (f x y : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x, Arg.expr y] none 
                    (explicit := false) (ellipsis := false)
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

-- generating distributions by combining

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

