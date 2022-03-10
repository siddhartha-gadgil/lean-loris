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

/- Basic functions for generation: at the level of expressions and arrays of expressions with degrees -/

/- Expression level combinations -/

/-- (optional) function application with unification -/
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

/-- (optional) application of function with unification to two arguments; for binary operations and relations -/
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

/-- (optional) function application without unification -/
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

/-- (optional) application of function without unification to two arguments; for binary operations and relations-/
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

/-- (optional) function application with unification given name of function -/
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

/-- (optional) function application with unification given name of function and a pair of arguments; for binary operations/relations -/
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


/-- copied from lean4 source code and modified; optionally returns proof that
 a rewritten expression is equal to the original one. -/
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

/-- transports a term using equlity if its type can be rewritten -/
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

/-- (optional) congrArg for an equality -/
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

/-- return Boolean pair (is-new, not-external), i.e., whether the element was encountered earlier, and, for "islands", whether the element was present "outside"  -/
class NewElem (α D: Type) where
  newElem: D → α → Nat → TermElabM (Bool × Bool)

/-- (optional) application of function with unification to two arguments; for binary operations and relations -/
def newElem{α D : Type}[c: NewElem α D](d : D)(a : α)(n : Nat) : 
    TermElabM (Bool × Bool) := c.newElem d a n

/-- set the new element functions as constants -/
def constNewElem{α D: Type}: Bool × Bool →  NewElem α D
  | ans => ⟨fun d a degBnd => pure ans⟩

/- Generating distributions, concretely arrays of expressions with degrees, by combining -/

/-- returns combinations of expressions with respect to an optional composition of pairs -/
def prodGenArrM{α β D: Type}[NewElem α D][nb : NewElem β D][ToMessageData α][ToMessageData β]
    (compose: α → β → TermElabM (Option Expr))
    (maxDegree : Nat)(card? : Option Nat)(fst: Array (α × Nat))(snd: Array (β × Nat))
    (data: D) : TermElabM ExprDist := do 
    if maxDegree > 0 then
      let mut fstTagGrouped: HashMap Nat (Array (α × Bool × Bool)) := HashMap.empty
      let mut sndTagGrouped: HashMap Nat (Array (β × Bool × Bool)) := HashMap.empty
      for (a, deg1) in fst do
        let prev := fstTagGrouped.findD deg1 #[]
        fstTagGrouped := fstTagGrouped.insert deg1 <| prev.push (a, ← newElem data a deg1)
      for (b, deg2) in snd do
        let prev := sndTagGrouped.findD deg2 #[]
        sndTagGrouped := sndTagGrouped.insert deg2 <| prev.push (b, ← newElem data b deg2)
      let fstAbove := degreeAbove fst maxDegree
      let sndAbove := degreeAbove snd maxDegree
      let mut withDegPairs : Array (α × β  × Nat) := #[]
      for deg1 in [0:maxDegree] do
        for deg2 in [0:maxDegree-deg1] do
          if leqOpt ((fstAbove.findD deg1 0) * (sndAbove.findD deg2 0)) card?
          then 
            for (e1, b1, be1) in fstTagGrouped.findD deg1 #[] do 
              for (e2, b2, be2) in sndTagGrouped.findD deg2 #[] do 
                  if (((b1 || b2))
                    || ((be1 || be2) && deg1 + deg2  + 1 = maxDegree)) 
                  then
                    withDegPairs := withDegPairs.push (e1, e2, deg1 + deg2  + 1)
      let arr1 : Array (TermElabM (Option (Expr × Nat))) := 
          withDegPairs.map <| fun (e1, e2, deg) => 
                (compose e1 e2).map (fun oe => 
                      oe.map (fun e4 => (e4, deg) ))
      let arr2 ←  arr1.filterMapM <| fun t => t
      let res ← ExprDist.fromArrayM arr2 
      return res
    else return ExprDist.empty

/-- returns combinations of expressions with respect to an optional composition of pairs that may return an array of expressions -/
def prodPolyGenArrM{α β D: Type}[NewElem α D][nb : NewElem β D][ToMessageData α][ToMessageData β]
    (compose: α → β → TermElabM (Option (Array Expr)))
    (maxDegree : Nat)(card? : Option Nat)(fst: Array (α × Nat))(snd: Array (β × Nat))
    (data: D) : TermElabM ExprDist := do 
    if maxDegree > 0 then
      let mut fstTagGrouped: HashMap Nat (Array (α × Bool × Bool)) := HashMap.empty
      let mut sndTagGrouped: HashMap Nat (Array (β × Bool × Bool)) := HashMap.empty
      for (a, deg1) in fst do
        let prev := fstTagGrouped.findD deg1 #[]
        fstTagGrouped := fstTagGrouped.insert deg1 <| prev.push (a, ← newElem data a deg1)
      for (b, deg2) in snd do
        let prev := sndTagGrouped.findD deg2 #[]
        sndTagGrouped := sndTagGrouped.insert deg2 <| prev.push (b, ← newElem data b deg2)
      let fstAbove := degreeAbove fst maxDegree
      let sndAbove := degreeAbove snd maxDegree
      let mut withDegPairs : Array (α × β  × Nat) := #[]
      for deg1 in [0:maxDegree] do
        for deg2 in [0:maxDegree-deg1] do
          if leqOpt ((fstAbove.findD deg1 0) * (sndAbove.findD deg2 0)) card?
          then 
            for (e1, b1, be1) in fstTagGrouped.findD deg1 #[] do 
              for (e2, b2, be2) in sndTagGrouped.findD deg2 #[] do 
                  if (((b1 || b2))
                    || ((be1 || be2) && deg1 + deg2  + 1 = maxDegree)) 
                  then
                    withDegPairs := withDegPairs.push (e1, e2, deg1 + deg2  + 1)
      let mut arr1 : Array (Option (Expr × Nat)) := #[]
      for (e1, e2, deg) in withDegPairs do 
        match ← compose e1 e2 with
        | none => pure ()
        | some a => 
          for e3 in a do 
            arr1 := arr1.push (some (e3, deg))        
      let arr2 :=  arr1.filterMap <| fun t => t
      let res ← ExprDist.fromArrayM arr2 
      return res
    else return ExprDist.empty

/-- returns combinations of expressions with respect to an optional composition of triples -/
def tripleProdGenArrM{α β γ  D: Type}[NewElem α D][NewElem β D][NewElem γ D]
    (compose: α → β → γ → TermElabM (Option Expr))
    (maxDegree : Nat)(card? : Option Nat)(fst: Array (α × Nat))(snd: Array (β × Nat))
    (third : Array (γ × Nat))(data: D) : TermElabM ExprDist := do 
    if maxDegree > 0 then
      let mut fstTagGrouped: HashMap Nat (Array (α × Bool × Bool)) := HashMap.empty
      let mut sndTagGrouped: HashMap Nat (Array (β × Bool × Bool)) := HashMap.empty
      let mut thirdTagGrouped: HashMap Nat (Array (γ × Bool × Bool)) := HashMap.empty
      for (a, deg1) in fst do
        let prev := fstTagGrouped.findD deg1 #[]
        fstTagGrouped := fstTagGrouped.insert deg1 <| prev.push (a, ← newElem data a deg1)
      for (b, deg2) in snd do
        let prev := sndTagGrouped.findD deg2 #[]
        sndTagGrouped := sndTagGrouped.insert deg2 <| prev.push (b, ← newElem data b deg2)
      for (c, w3) in third do
        let prev := thirdTagGrouped.findD w3 #[]
        thirdTagGrouped := thirdTagGrouped.insert w3 <| prev.push (c, ← newElem data c w3) 
      let fstAbove := degreeAbove fst maxDegree
      let sndAbove := degreeAbove snd maxDegree
      let thirdAbove := degreeAbove third maxDegree    
      let mut withDegTriples : Array (α × β × γ  × Nat) := #[]
      for deg1 in [0:maxDegree] do
        for deg2 in [0:maxDegree-deg1] do
          for w3 in [0:maxDegree-deg1-deg2] do
          if leqOpt ((fstAbove.findD deg1 0) * (sndAbove.findD deg2 0) * (thirdAbove.findD w3 0)) card?
          then 
            for (e1, b1, be1) in fstTagGrouped.findD deg1 #[] do 
              for (e2, b2, be2) in sndTagGrouped.findD deg2 #[] do 
                for (e3, b3, be3) in thirdTagGrouped.findD w3 #[] do 
                  if (((b1 || b2 || b3))
                    || ((be1 || be2 || be3) && deg1 + deg2 + w3 + 1 = maxDegree)) 
                  then
                    withDegTriples := withDegTriples.push (e1, e2, e3, deg1 + deg2 + w3 + 1)
      let arr1 : Array (TermElabM (Option (Expr × Nat))) := 
          withDegTriples.map <| fun (e1, e2, e3, deg) => 
                (compose e1 e2 e3).map (fun oe => 
                      oe.map (fun e4 => (e4, deg) ))
      let arr2 ←  arr1.filterMapM <| fun t => t
      let res ← ExprDist.fromArrayM arr2
      return res
    else return ExprDist.empty

