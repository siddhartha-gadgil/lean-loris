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
    let h ← mkMVar head
    let headType ← inferType h
    withLocalDecl Name.anonymous BinderInfo.default headType  $ fun x => 
      do
        assignExprMVar head x
        let prev ← mvarToLambda tail value
        let res ← mkLambdaFVars #[x] prev
        let res ← whnf res
        Term.synthesizeSyntheticMVarsNoPostponing
        return res

def tacticLambda(tactic : MVarId → MetaM (List MVarId))(goalType: Expr) : 
      TermElabM <| Option Expr := do
      let goal ← mkFreshExprMVar (some goalType)
      let goalId := goal.mvarId!
      try
        let mvars ← tactic goalId
        some <| ←  mvarToLambda mvars goal
      catch _ => none

-- for finishing tactics
def tacticGet(tactic : MVarId → MetaM (List MVarId))(goalType: Expr) : 
      TermElabM <| Option Expr := do
      let goal ← mkFreshExprMVar (some goalType)
      let goalId := goal.mvarId!
      try
        let mvars ← tactic goalId
        if mvars.isEmpty then
          let res ← whnf goal
          Term.synthesizeSyntheticMVarsNoPostponing
          some res
        else
          none
      catch _ => none

def tacticLambdaMVars(tactic : MVarId → MetaM (List MVarId))(goalType: Expr) : 
      TermElabM <| Option (Expr × (List MVarId)) := do
      let goal ← mkFreshExprMVar (some goalType)
      let goalId := goal.mvarId!
      try
        let mvars ← tactic goalId
        some <| (←  mvarToLambda mvars goal, mvars)
      catch _ => none


def relGoalTypes(mvars: List MVarId) : TermElabM (List Expr) := do
  match mvars with
  | [] => pure []
  | head :: tail => do
    let h ← mkMVar head
    let headType ← inferType h
    let headType ← whnf headType
    Term.synthesizeSyntheticMVarsNoPostponing
    withLocalDecl Name.anonymous BinderInfo.default headType  $ fun x => 
      do
        let prevBase ← relGoalTypes tail
        let prev ← prevBase.mapM <| fun type => mkForallFVars #[x] type
        return (headType :: prev)

def indepGoalTypes(mvars: List MVarId) : TermElabM (List Expr) := do
  match mvars with
  | [] => pure []
  | head :: tail => do
    let h ← mkMVar head
    let headType ← inferType h
    let headType ← whnf headType
    Term.synthesizeSyntheticMVarsNoPostponing
    let prev ← indepGoalTypes tail
    return (headType :: prev)

def tacticExprArray(tactic : MVarId → MetaM (List MVarId))(indepGoals: Bool)
  (goalType: Expr) : 
      TermElabM <| Option (Array Expr) := do
      let lmv ← tacticLambdaMVars tactic goalType
      lmv.mapM fun (l, mvarIds) => do
        let mvars ← if indepGoals then indepGoalTypes mvarIds else relGoalTypes mvarIds
        (l :: mvars).toArray

def typeSumEvolverM{D: Type}(types : Nat → Nat → D → ExprDist → 
  TermElabM (Array (Expr × Nat)))
          (tacList : Expr → TermElabM (Option (Array Expr))) : EvolverM D := 
            fun wb cb data dist => do
            let typeArray ← types wb cb data dist
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, w) in typeArray do
              match ← tacList type with
              | none => ()
              | some ys =>
                for y in ys do terms := terms.push (y, w)
            ExprDist.fromArray terms

def typeOptEvolverM{D: Type}(types : Nat → Nat → D → ExprDist →
         TermElabM (Array (Expr × Nat)))
          (tacOpt : Expr → TermElabM (Option Expr)) : EvolverM D := 
            fun wb cb data dist => do
            let typeArray ← types wb cb data dist
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, w) in typeArray do
              match ← tacOpt type with
              | none => ()
              | some y =>
                terms := terms.push (y, w)
            ExprDist.fromArray terms

def tacticTypeEvolverM{D: Type}(tactic : MVarId → MetaM (List MVarId))(indepGoals: Bool) :
    EvolverM D := 
      typeSumEvolverM (fun wb cb data dist => (dist.bound wb cb).typesArr) 
        (tacticExprArray tactic indepGoals)

def tacticPropEvolverM{D: Type}(tactic : MVarId → MetaM (List MVarId))(indepGoals: Bool) :
    EvolverM D := 
      typeSumEvolverM (fun wb cb data dist => (dist.bound wb cb).propsArr) 
        (tacticExprArray tactic indepGoals)

def optProofTypeEvolverM{D: Type}(tacOpt : Expr → TermElabM (Option Expr)) : 
    EvolverM D := 
      typeOptEvolverM (fun wb cb data dist => (dist.bound wb cb).typesArr) 
        tacOpt

def optProofPropEvolverM{D: Type}(tacOpt : Expr → TermElabM (Option Expr)) : 
    EvolverM D := 
      typeOptEvolverM (fun wb cb data dist => (dist.bound wb cb).propsArr) 
        tacOpt

def forallIsleM {D: Type}[IsleData D](type: Expr)(typedEvolve : Expr → EvolverM D)
    (weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D): TermElabM (ExprDist) := 
      forallTelescope type <| fun xs y => do
      let isleInit ← xs.foldlM (fun d x => d.updateExprM x 0) init
      let isleFinal ← typedEvolve y weightBound cardBound initData isleInit
      isleFinal.mapM <| fun e => mkLambdaFVars xs e

def forallBoundedIsleM {D: Type}[IsleData D](bound: Nat)(type: Expr)
    (typedEvolve : Expr → EvolverM D)
    (weightBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D): TermElabM (ExprDist) := 
      forallBoundedTelescope type (some bound) <| fun xs y => do
      let isleInit ← xs.foldlM (fun d x => d.updateExprM x 0) init
      let isleFinal ← typedEvolve y weightBound cardBound initData isleInit
      isleFinal.mapM <| fun e => mkLambdaFVars xs e

open Nat

def natRec {Q : Nat → Sort u} :
    (Q 0) → ((n: Nat) → (Q n → Q (n + 1))) → (n: Nat) →  (Q n) := 
    fun z step n => 
      match n with
      | zero => z
      | succ k => step k (natRec z step k)

def natRecTac: MVarId → MetaM (List MVarId) := 
  fun mid => 
      apply mid <| mkConst ``natRec


def decideGet (goalType: Expr) : 
      TermElabM <| Option Expr := do
      try
        let pf ← mkDecideProof goalType
        some <| pf
      catch _ => none

def rflGet(goalType: Expr) : 
      TermElabM <| Option Expr := do
      match goalType.eq? with
      | some (α , lhs, rhs) =>
        if ← isDefEq lhs rhs then
          return some <| ←  mkApp (mkConst ``Eq.refl) lhs 
        else
          return none
      | _  => none

-- tests

#check Eq.refl

def pp : Prop := 1 = 2

#eval isProp (mkConst ``pp)
#eval isProp (mkConst ``Nat)
#eval isType (mkConst ``Nat)
#eval isType (mkConst ``pp)
#check Expr.isForall

def sumEl : TermElabM Expr := do 
  let mvar1 ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvar2 ← mkFreshExprMVar (some (mkConst ``Nat)) -- none works too
  let value ← mkAppM ``Nat.add #[mvar1, mvar2]
  let mvar ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvarId ← mvar.mvarId!
  assignExprMVar mvarId value
  metaToLambda [mvar1, mvar2] mvar

#eval sumEl

syntax(name:=sm) "sumEl!" : term
@[termElab sm] def smImpl : TermElab := fun _ _ =>
    sumEl

#eval sumEl! 1 2

#check Meta.induction
#check Meta.apply 
#check liftMetaTactic
#check forallTelescope
#check @Exists

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

#eval factorial 5
example : 1 = 1 := by exact rfl
#check rfl