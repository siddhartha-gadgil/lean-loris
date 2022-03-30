import LeanLoris.Evolution
import Lean.Meta
import Lean.Elab
open Lean Meta Elab Tactic Term

/- 
Evolovers based on tactics, with propositions (or all types) in an `ExprDist` viewed as goals.
-/

/-- λ-expression with respect to meta variables of an expression -/
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

/-- λ-expression with respect to meta variables of a meta variable -/
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

/-- given a `tactic` at the `Elab` level, returns a λ-expression corresponding to applying the tactic if successful -/
def tacticLambda(tactic : MVarId → TermElabM (List MVarId))(goalType: Expr) : 
      TermElabM <| Option Expr := do
      let goal ← mkFreshExprMVar (some goalType)
      let goalId := goal.mvarId!
      try
        let mvars ← tactic goalId
        return some <| ←  mvarToLambda mvars goal
      catch _ => pure none

/-- given a finishing `tactic` at the `Elab` level, returns a solution if successful -/
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

/-- given a `tactic` at the `Elab` level, returns a λ-expression corresponding to applying the tactic if successful -/
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
        return none

/-- given mvars (representing goals) form expressions for their types with later types as λ-expressions in earlier types -/
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

/-- given mvars (representing goals) form expressions for their types assuming goals are independent (no λs formed) -/
def indepGoalTypes(mvars: List Expr) : TermElabM (List Expr) := do
  match mvars with
  | [] => pure []
  | head :: tail => do
    let headType ← inferType head
    let headType ← whnf headType
    Term.synthesizeSyntheticMVarsNoPostponing
    let prev ← indepGoalTypes tail
    return (headType :: prev)

/-- given tactic at the `Elab` level and an expression for a goal, returns a collection of expressions giving derived goals and an expression giving the original goal in terms of the new ones, if the tactic is successful -/
def tacticExprArray(tactic : MVarId → TermElabM (List MVarId))(indepGoals: Bool)
  (goalType: Expr) : 
      TermElabM <| Option (Array Expr) := do
      let lmv ← tacticLambdaMVars tactic goalType
      lmv.mapM fun (l, mvars) => do
        let mvars ← if indepGoals then indepGoalTypes mvars else relGoalTypes mvars
        return (l :: mvars).toArray

/-- sum over types and tactics of derived goals -/
def typeSumEvolverM{D: Type}(types : Nat → Option Nat → D → ExprDist → 
  TermElabM (Array (Expr × Nat)))
          (tacList : Expr → TermElabM (Option (Array Expr))) : EvolverM D := 
            fun degBnd cb data dist => do
            let typeArray ← types degBnd cb data dist
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, deg) in typeArray do
              match ← tacList type with
              | none =>
                pure ()
              | some ys =>
                for y in ys do terms := terms.push (y, deg + 1)
            ExprDist.fromArrayM terms

/-- sum over given types with degrees and tactics of derived goals -/
def withDegTypeSumEvolverM{D: Type}(types : Nat → Option Nat → D → ExprDist → 
  TermElabM (Array (Expr × Nat)))
          (tacList : Expr → TermElabM (Option (Array (Expr × Nat)))) : EvolverM D := 
            fun degBnd cb data dist => do
            let typeArray ← types degBnd cb data dist
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, deg) in typeArray do
              match ← tacList type with
              | none =>
                pure ()
              | some ys =>
                for (y, w0) in ys do terms := terms.push (y, deg + w0)
            ExprDist.fromArrayM terms

/-- sum over given types with degrees and optional tactics of derived goals -/
def typeOptEvolverM{D: Type}(types : Nat → Option Nat → D → ExprDist →
         TermElabM (Array (Expr × Nat)))
          (tac? : Expr → TermElabM (Option Expr)) : EvolverM D := 
            fun degBnd cb data dist => do
            let typeArray ← types degBnd cb data dist
            let mut terms : Array (Expr × Nat) := Array.empty
            for (type, deg) in typeArray do
              match ← tac? type with
              | none => pure ()
              | some y =>
                terms := terms.push (y, deg)
            ExprDist.fromArrayM terms

/-- sum over all types derived goals from a tactic -/
def tacticTypeEvolverM{D: Type}(tactic : MVarId → TermElabM (List MVarId))(indepGoals: Bool) :
    EvolverM D := 
      typeSumEvolverM (fun degBnd cb data dist => do (← dist.boundM degBnd cb).typesArr) 
        (tacticExprArray tactic indepGoals)

/-- sum over all propositions derived goals from a tactic -/
def tacticPropEvolverM{D: Type}(tactic : MVarId → TermElabM (List MVarId))(indepGoals: Bool) :
    EvolverM D := 
      typeSumEvolverM (fun degBnd cb data dist => do  (← dist.boundM degBnd cb).propsArr) 
        (tacticExprArray tactic indepGoals)

/-- sum over all types derived goals from an optional tactic -/
def optProofTypeEvolverM{D: Type}(tac? : Expr → TermElabM (Option Expr)) : 
    EvolverM D := 
      typeOptEvolverM (fun degBnd cb data dist => do (← dist.boundM degBnd cb).typesArr) 
        tac?

/-- sum over all propositions derived goals from an optional tactic -/
def optProofPropEvolverM{D: Type}(tac? : Expr → TermElabM (Option Expr)) : 
    EvolverM D := 
      typeOptEvolverM (fun degBnd cb data dist => 
        do (← dist.boundM degBnd cb).propsArr) 
        tac?

/-- auxiliary function for apply-based evolver-/
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

/-- lifting `apply` tactic to an evolver -/
def applyTacticEvolver(D: Type)[NewElem Expr D] : EvolverM D := 
  fun degBnd c d init => 
  do
    prodPolyGenArrM applyPairing degBnd c (← init.typesArr) (← init.funcs) d

/-- generated with evolvers depending on a type within forall-/
def forallIsleM {D: Type}[IsleData D](type: Expr)(typedEvolve : Expr → EvolverM D)
    (degreeBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D): TermElabM ExprDist := 
      forallTelescope type <| fun xs y => do
      let isleInit ← xs.foldlM (fun d x => d.updateExprM x 0) init
      let isleFinal ← typedEvolve y degreeBound cardBound 
            (isleData initData init degreeBound cardBound) isleInit
      isleFinal.mapM <| fun e => mkLambdaFVars xs e

/-- generated with evolvers depending on a type within bounded forall-/
def forallBoundedIsleM {D: Type}[IsleData D](bound: Nat)(type: Expr)
    (typedEvolve : Expr → EvolverM D)
    (degreeBound: Nat)(cardBound: Nat)
      (init : ExprDist)(initData: D): TermElabM ExprDist := 
      forallBoundedTelescope type (some bound) <| fun xs y => do
      let isleInit ← xs.foldlM (fun d x => d.updateExprM x 0) init
      let isleFinal ← typedEvolve y degreeBound cardBound 
          (isleData initData init degreeBound cardBound) isleInit
      isleFinal.mapM <| fun e => mkLambdaFVars xs e

/-- get from decide tactic -/
def decideGet (goalType: Expr) : 
      TermElabM <| Option Expr := do
      try
        let pf ← mkDecideProof goalType
        return some <| pf
      catch _ => return none

/-- get by reflexivity -/
def rflGet(goalType: Expr) : 
      TermElabM <| Option Expr := do
      match goalType.eq? with
      | some (α , lhs, rhs) =>
        if ← isDefEq lhs rhs then
          return some <| ←  mkAppM ``Eq.refl #[lhs] 
        else
          return none
      | _  => return none

/-- reflexivity evolver -/
def rflEvolverM(D: Type) : EvolverM D :=
  optProofPropEvolverM rflGet

open Nat

universe u

/-- recursion function for natural numbers (to bypass no code generation) -/
def natRec (Q : Nat → Sort u) :
    (Q 0) → ((n: Nat) → (Q n → Q (n + 1))) → (n: Nat) →  (Q n) := 
    fun z step n => 
      match n with
      | zero => z
      | succ k => step k (natRec Q z step k)

-- auxiliary function for natRec matching
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

-- auxiliary function for natRec matching
def natRecStep(fmly: Nat → Sort u) := ∀n: Nat, fmly n → fmly (n + 1) 

/-- Evolver for recursion with natural numbers -/
def natRecEvolverM(D: Type) : EvolverM D := 
  let tactic : Expr → TermElabM (Option (Array (Expr× Nat))) := 
    fun type => 
      do
      let fmly? ← natRecFamily type
      fmly?.mapM <| fun fmly =>
        return #[(← mkAppM ``natRec #[fmly], 0), 
        (← whnf <| mkApp fmly (mkConst ``Nat.zero), 1), 
        (← whnf <| ← mkAppM ``natRecStep #[fmly], 1)] 
  withDegTypeSumEvolverM (fun degBnd cb data dist => 
    do (← dist.boundM degBnd cb).goalsArr) tactic

