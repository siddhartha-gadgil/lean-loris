import LeanLoris.Evolution
import Lean.Meta
import Lean.Elab
open Lean Meta Elab Tactic Term

def metaToLambda(mvars: List Expr)(value: Expr) : TermElabM Expr := do
  match mvars with
  | [] => pure value
  | head :: tail =>
    let headId := head.mvarId!
    let headType ← inferType head
    withLocalDecl Name.anonymous BinderInfo.default headType  $ fun x => 
      do
        assignExprMVar headId x
        let prev ← metaToLambda tail value
        let res ← mkLambdaFVars #[x] prev
        Term.synthesizeSyntheticMVarsNoPostponing
        return res

def mvarToLambda(mvars: List MVarId)(value: Expr) : TermElabM Expr := do
  match mvars with
  | [] => pure value
  | head :: tail =>
    let h := mkMVar head
    let headType ← inferType h
    withLocalDecl Name.anonymous BinderInfo.default headType  $ fun x => 
      do
        assignExprMVar head x
        let prev ← mvarToLambda tail value
        let res ← mkLambdaFVars #[x] prev
        let res ← whnf res
        Term.synthesizeSyntheticMVarsNoPostponing
        return res

def tacticLambda(tactic : MVarId → TermElabM (List MVarId))(goalType: Expr) : 
      TermElabM <| Option Expr := do
      let goal ← mkFreshExprMVar (some goalType)
      let goalId := goal.mvarId!
      try
        let mvars ← tactic goalId
        return some <| ←  mvarToLambda mvars goal
      catch _ => pure none

-- for finishing tactics
def tacticGet(tactic : MVarId → TermElabM (List MVarId))(goalType: Expr) : 
      TermElabM <| Option Expr := do
      let goal ← mkFreshExprMVar (some goalType)
      let goalId := goal.mvarId!
      try
        let mvars ← tactic goalId
        if mvars.isEmpty then
          let res ← whnf goal
          Term.synthesizeSyntheticMVarsNoPostponing
          return some res
        else
          return none
      catch _ => return none

def tacticLambdaMVars(tactic : MVarId → TermElabM (List MVarId))(goalType: Expr) : 
      TermElabM <| Option (Expr × (List Expr)) := do
      let goal ← mkFreshExprMVar (some goalType)
      let goal ← whnf goal
      Term.synthesizeSyntheticMVarsNoPostponing
      let goalId := goal.mvarId!
      try
        let mvars ← tactic goalId
        let mvars ← mvars.mapM fun id => do
              let z := mkMVar id
              let z ← whnf z
              Term.synthesizeSyntheticMVarsNoPostponing
              pure z
        -- let goal ← whnf goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return some <| (←  metaToLambda mvars goal, mvars)
      catch exc =>
        -- logInfo m!"tacticLambdaMVars failed for {goal}: ${exc.toMessageData}"
        return none


def relGoalTypes(mvars: List Expr) : TermElabM (List Expr) := do
  match mvars with
  | [] => pure []
  | head :: tail => do
    let headType ← inferType head
    let headType ← whnf headType
    Term.synthesizeSyntheticMVarsNoPostponing
    withLocalDecl Name.anonymous BinderInfo.default headType  $ fun x => 
      do
        let prevBase ← relGoalTypes tail
        let prev ← prevBase.mapM <| fun type => mkForallFVars #[x] type
        return (headType :: prev)

def indepGoalTypes(mvars: List Expr) : TermElabM (List Expr) := do
  match mvars with
  | [] => pure []
  | head :: tail => do
    let headType ← inferType head
    let headType ← whnf headType
    Term.synthesizeSyntheticMVarsNoPostponing
    let prev ← indepGoalTypes tail
    return (headType :: prev)

def tacticExprArray(tactic : MVarId → TermElabM (List MVarId))(indepGoals: Bool)
  (goalType: Expr) : 
      TermElabM <| Option (Array Expr) := do
      let lmv ← tacticLambdaMVars tactic goalType
      lmv.mapM fun (l, mvars) => do
        let mvars ← if indepGoals then indepGoalTypes mvars else relGoalTypes mvars
        return (l :: mvars).toArray

def typeSumEvolverM{D: Type}(types : Nat → Nat → D → ExprDist → 
  TermElabM (Array (Expr × Nat)))
          (tacList : Expr → TermElabM (Option (Array Expr))) : EvolverM D := 
            fun wb cb data dist => do
            let typeArray ← types wb cb data dist
            -- logInfo m!"applying tactic to {typeArray.size} types: {typeArray}"
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, w) in typeArray do
              match ← tacList type with
              | none =>
                -- logInfo m!"tactic failed for {type}" 
                pure ()
              | some ys =>
                -- logInfo m!"tactic succeeded for {type}, giving {ys}"
                -- logInfo m!"head type : {← inferType ys[0]}" 
                for y in ys do terms := terms.push (y, w + 1)
            ExprDist.fromArrayM terms

def weightedTypeSumEvolverM{D: Type}(types : Nat → Nat → D → ExprDist → 
  TermElabM (Array (Expr × Nat)))
          (tacList : Expr → TermElabM (Option (Array (Expr × Nat)))) : EvolverM D := 
            fun wb cb data dist => do
            let typeArray ← types wb cb data dist
            -- logInfo m!"applying tactic to {typeArray.size} types: {typeArray}"
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, w) in typeArray do
              match ← tacList type with
              | none =>
                -- logInfo m!"tactic failed for {type}" 
                pure ()
              | some ys =>
                -- logInfo m!"tactic succeeded for {type}, giving {ys}"
                -- logInfo m!"head type : {← inferType ys[0].1}" 
                for (y, w0) in ys do terms := terms.push (y, w + w0)
            ExprDist.fromArrayM terms

def typeOptEvolverM{D: Type}(types : Nat → Nat → D → ExprDist →
         TermElabM (Array (Expr × Nat)))
          (tac? : Expr → TermElabM (Option Expr)) : EvolverM D := 
            fun wb cb data dist => do
            let typeArray ← types wb cb data dist
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, w) in typeArray do
              match ← tac? type with
              | none => pure ()
              | some y =>
                terms := terms.push (y, w)
            ExprDist.fromArrayM terms

def tacticTypeEvolverM{D: Type}(tactic : MVarId → TermElabM (List MVarId))(indepGoals: Bool) :
    EvolverM D := 
      typeSumEvolverM (fun wb cb data dist => (dist.bound wb cb).typesArr) 
        (tacticExprArray tactic indepGoals)

def tacticPropEvolverM{D: Type}(tactic : MVarId → TermElabM (List MVarId))(indepGoals: Bool) :
    EvolverM D := 
      typeSumEvolverM (fun wb cb data dist => (dist.bound wb cb).propsArr) 
        (tacticExprArray tactic indepGoals)

def optProofTypeEvolverM{D: Type}(tac? : Expr → TermElabM (Option Expr)) : 
    EvolverM D := 
      typeOptEvolverM (fun wb cb data dist => (dist.bound wb cb).typesArr) 
        tac?

def optProofPropEvolverM{D: Type}(tac? : Expr → TermElabM (Option Expr)) : 
    EvolverM D := 
      typeOptEvolverM (fun wb cb data dist => (dist.bound wb cb).propsArr) 
        tac?

def applyPairing(type func: Expr) : TermElabM (Option (Array Expr)) := do
  let goal ← mkFreshExprMVar (some type)
  let goalId := goal.mvarId!
  try 
    let mvarIds ← Meta.apply goalId func
    let newGoals ← relGoalTypes (mvarIds.map (fun id => mkMVar id))
    let goalLambda ← 
      mvarToLambda mvarIds goal
    return some (goalLambda :: newGoals).toArray
  catch _ => return none

def applyTacticEvolver(D: Type)[IsNew D][NewElem Expr D] : EvolverM D := 
  fun wb c d init => 
  do
    prodPolyGenArrM applyPairing wb c (← init.typesArr) (← init.funcs) d



def forallIsleM {D: Type}[IsleData D](type: Expr)(typedEvolve : Expr → EvolverM D)
    (weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D): TermElabM ExprDist := 
      forallTelescope type <| fun xs y => do
      let isleInit ← xs.foldlM (fun d x => d.updateExprM x 0) init
      let isleFinal ← typedEvolve y weightBound cardBound 
            (isleData initData init weightBound cardBound) isleInit
      isleFinal.mapM <| fun e => mkLambdaFVars xs e

def forallBoundedIsleM {D: Type}[IsleData D](bound: Nat)(type: Expr)
    (typedEvolve : Expr → EvolverM D)
    (weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D): TermElabM ExprDist := 
      forallBoundedTelescope type (some bound) <| fun xs y => do
      let isleInit ← xs.foldlM (fun d x => d.updateExprM x 0) init
      let isleFinal ← typedEvolve y weightBound cardBound 
          (isleData initData init weightBound cardBound) isleInit
      isleFinal.mapM <| fun e => mkLambdaFVars xs e

def decideGet (goalType: Expr) : 
      TermElabM <| Option Expr := do
      try
        let pf ← mkDecideProof goalType
        return some <| pf
      catch _ => return none

def rflGet(goalType: Expr) : 
      TermElabM <| Option Expr := do
      match goalType.eq? with
      | some (α , lhs, rhs) =>
        if ← isDefEq lhs rhs then
          return some <| ←  mkAppM ``Eq.refl #[lhs] 
        else
          return none
      | _  => return none

def rflEvolverM(D: Type) : EvolverM D :=
  optProofPropEvolverM rflGet

open Nat

universe u

def natRec (Q : Nat → Sort u) :
    (Q 0) → ((n: Nat) → (Q n → Q (n + 1))) → (n: Nat) →  (Q n) := 
    fun z step n => 
      match n with
      | zero => z
      | succ k => step k (natRec Q z step k)

def natRecFamily(type: Expr) : TermElabM (Option Expr) := do 
  let u ← mkFreshLevelMVar
  let family ←  mkArrow (mkConst ``Nat) (mkSort u)
  let fmlyVar ← mkFreshExprMVar (some family)
  let piType ← 
    withLocalDecl Name.anonymous BinderInfo.default (mkConst ``Nat)  $ fun x =>
      mkForallFVars #[x] (mkApp fmlyVar x)
  if ← isDefEq piType type then
    Term.synthesizeSyntheticMVarsNoPostponing
    whnf fmlyVar
  else
    return none

def natRecStep(fmly: Nat → Sort u) := ∀n: Nat, fmly n → fmly (n + 1) 

def natRecEvolverM(D: Type) : EvolverM D := 
  let tactic : Expr → TermElabM (Option (Array (Expr× Nat))) := 
    fun type => 
      do
      let fmly? ← natRecFamily type
      fmly?.mapM <| fun fmly =>
        return #[(← mkAppM ``natRec #[fmly], 0), 
        (← whnf <| mkApp fmly (mkConst ``Nat.zero), 1), 
        (← whnf <| ← mkAppM ``natRecStep #[fmly], 1)] 
  weightedTypeSumEvolverM (fun wb cb data dist => (dist.bound wb cb).goalsArr) tactic

def egProp := ∀ n: Nat, n = n

def egFamily := natRecFamily <| mkConst `egProp

-- #eval egFamily

def pp : Prop := 1 = 2

-- #eval isProp (mkConst ``pp)
-- #eval isProp (mkConst ``Nat)
-- #eval isType (mkConst ``Nat)
-- #eval isType (mkConst ``pp)
-- #check Expr.isForall

def sumEl : TermElabM Expr := do 
  let mvar1 ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvar2 ← mkFreshExprMVar (some (mkConst ``Nat)) -- none works too
  let value ← mkAppM ``Nat.add #[mvar1, mvar2]
  let mvar ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvarId := mvar.mvarId!
  assignExprMVar mvarId value
  metaToLambda [mvar1, mvar2] mvar

-- #eval sumEl

elab "sumEl!" : term => sumEl

#eval sumEl! 1 2

theorem constFn2{α : Type}(f: Nat → α):
    (∀ n : Nat, f n = f (n + 1)) →
    (∀ n : Nat, f n = f 0) := by
      intro hyp 
      apply natRec
      focus
        rfl
      focus
        intro n ih 
        rw [← hyp]
        assumption

def factorial : Nat →  Nat := by
  apply natRec
  focus
    exact 1
  focus
    intro n ih
    exact ((n + 1) * ih)

-- #eval factorial 5
example : 1 = 1 := by exact rfl
