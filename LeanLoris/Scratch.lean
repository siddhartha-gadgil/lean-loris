import Lean.Meta
import Lean.Elab
import Std
open Lean Meta Elab 
open Nat Std

/-
Miscellaneous experiments, not used in the main code.
-/

def slowFib (id : Nat) : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => dbgTrace s!"fib {id}" fun _ => slowFib id n + slowFib id (n+1)

-- def conc : Nat := 
--   let t1 := Task.spawn fun _ => slowFib 1 32
--   let t2 := Task.spawn fun _ => slowFib 2 32
--   let t3 := Task.spawn fun _ => slowFib 3 33
--   let t4 := Task.spawn fun _ => slowFib 4 34
--   t1.get + t2.get + t3.get + t4.get

-- #eval conc

def conc2 : Nat :=
  let arr := #[1, 3, 4, 5, 6]
  let tsks := arr.map fun n => Task.spawn fun _ => slowFib n (30 + n)
  let res := tsks.map fun t => t.get
  res.foldl (fun acc n => acc + n) 0

-- #eval conc2

def exprSeq : TermElabM (Array Expr) := do
  let mut arr := Array.mk []
  for i in [0:400000] do
    let e := ToExpr.toExpr (i % 100)
    arr := arr.push e
  return arr

def count (e: Expr) : TermElabM Nat := do
  let arr ← exprSeq
  let farr ← arr.filterM <| fun exp => isDefEq exp e 
  return farr.size

def countsSerial: TermElabM (Array Nat) := do
  let mut arr : Array Nat := #[]
  for i in [0:8] do arr := arr.push i
  let cntsAux := arr.map <| fun i => count (ToExpr.toExpr i)
  let cnts ←  cntsAux.mapM <| fun t => t
  return cnts

def counts: TermElabM (Array Nat) := do
  let arr : Array Nat := #[1, 2, 3, 4, 5, 6]
  let cntsAux := arr.map <| fun i => Task.spawn fun _ => count (ToExpr.toExpr i)
  let cntsAux2 := cntsAux.map <| fun t => t.get
  let cnts ←  cntsAux.mapM <| fun t => t.get
  return cnts

def countIO (env: Environment)(n: Nat) : IO (Option Nat) := do
    let el := count (ToExpr.toExpr n)
    let m := el.run'
    let c := m.run'
    let ei := c.run' {maxHeartbeats := 100000000000} {env}
    match ←  ei.toIO' with
  | Except.ok n => 
      return some n
  | Except.error e =>
      return none

set_option maxHeartbeats 100000000

def countsPar(env: Environment) : IO (Nat) := do
  let arr : Array Nat := #[1, 2, 3, 4, 5, 6]
  let eg ←  (countIO env 3).asTask.toIO
  let ego := eg.get
  let egopt := match ego with
      | Except.ok n => n
      | Except.error e => none 
  let cntsAux := arr.map <| fun i =>  
    ((countIO env i).asTask (Task.Priority.dedicated)).toIO
  let cnts ←  cntsAux.mapM <| fun iot => do 
        let tsk ← iot
        let eio := tsk.get
        match eio with
          | Except.ok n => return n
          | Except.error e => return none
  let total := cnts.foldl (fun acc nopt => 
      match nopt with
      | some k => acc + k 
      | none => acc) 0
  return total

def countsM : MetaM Nat := do
  countsPar (← getEnv)

-- #eval countsM

open Nat

theorem constFn{α : Type}(f: Nat → α):
    (∀ n : Nat, f n = f (n + 1)) →
    (∀ n : Nat, f n = f 0) := by
      intro hyp n
      induction n with
      | zero => rfl
      | succ k ih => 
        rw [← hyp]
        assumption
      
@[inline] def averageBy
    [Add α] [HDiv α Nat α] [HAdd α α $ outParam α] [Inhabited α] [OfNat α 0]
    (projection: β → α) : List β  → α
  | [] => panic! "invalid argument exception: may not provide empty list"
  | xs =>
    let sum : α := xs.foldr (fun x y => (projection x) + y) 0
    let length := xs.length
    sum / length

example : Unit := Id.run for x in [1, 2, 3, 4, 5] do return ()
  
#check forIn [1, 2] 3 
#check ForIn
#check @List.forIn

def ForIn.mkArray [ForIn Id α β] (l: α):  Array β := Id.run do
  let mut arr := Array.mk []
  for x in l do
    arr := arr.push x
  return arr

#check List

universe u
class Iterable (l: Type u)(α : Type u) where
  toArray : l  → Array α

class IterableFamily (l: Type u → Type u) where
  toArray : l α  → Array α

instance {l: Type u → Type u}[it : IterableFamily l] (α : Type u) : Iterable (l α) α :=
  ⟨fun x => it.toArray x⟩

instance : IterableFamily List    :=
  ⟨fun l => l.toArray⟩

instance : IterableFamily Array   :=
  ⟨fun l => l⟩

def mkArray [it : Iterable l α] (x: l): Array α :=
  it.toArray x

def mkList [it : Iterable l α] (x: l): List α :=
  (mkArray x).toList

def mkHashMap 
  [it : Iterable l  (α × β )][Hashable α][BEq α][BEq β](x: l ): HashMap α β   :=
    let arr : Array (α × β) := mkArray x
    arr.foldl (fun acc (k, v) => acc.insert k v) HashMap.empty

def ForIn.toArray [ForIn Id l α](x : l): (Array α) := Id.run
  do
    let mut arr := Array.mk []
    for a in x do
      arr := arr.push a 
    return arr

instance {l α : Type}[ForIn Id l α] : Iterable l α :=
  ⟨fun x => ForIn.toArray x⟩

def r : Range := [0:3]
def arr : Array Nat := mkArray r

#check Range

open Nat

example (x y w: Nat)(f g: Nat → Nat): x * f y = g w * f z := by
  apply congr
  focus
    exact sorry
  focus
    apply congr
    focus
      apply Eq.refl
    exact sorry

#check fun mvar => Meta.apply mvar (mkConst ``congr)

def tryCloseGoal (mvar: MVarId) : MetaM Bool := do
  let u ← mkFreshLevelMVar
  try 
    let res ←  Meta.apply mvar (mkConst ``Eq.refl [u])
    unless res.isEmpty do
      throwError "failed to close goal"
    pure true
  catch _ => 
  try 
    let res ←  Meta.apply mvar (mkConst ``Subsingleton.intro [u])
    unless res.isEmpty do
      throwError "failed to close goal"
    pure true
  catch _ =>
    pure false

def congrStep? (mvar: MVarId) : MetaM (Option (List MVarId)) := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let closed  ← tryCloseGoal mvar
  if !closed then 
    try
      let res ←  Meta.apply mvar (mkConst ``congr [u, v])
      return some res
    catch e => 
      pure none
  else 
    pure none

partial def recCongr(maxDepth? : Option Nat)(mvar: MVarId) : MetaM (List MVarId) := do
  let closeOnly : Bool := (maxDepth?.map (fun n => decide (n ≤  1))).getD false
  if closeOnly then
    let  chk ← tryCloseGoal mvar
    if chk then return [] else return [mvar]
  let res ← congrStep? mvar
  match res with
  | some [] => return []
  | some xs => do
    let depth? := maxDepth?.map (fun n => n - 1)
    let groups ← xs.mapM (recCongr depth?)
    return groups.bind id
  | none => return [mvar]

def Meta.congr(maxDepth? : Option Nat)(mvar : MVarId) : MetaM (List MVarId) := do
  try 
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let xs ← Meta.apply mvar (mkConst ``congr [u, v])
    let groups ← xs.mapM (recCongr maxDepth?)
    return groups.bind id
  catch e =>
    throwTacticEx `congr mvar e.toMessageData

open Lean.Elab.Tactic

/--
The `congr` tactic attempts to identify both sides of an equality goal `A = B`, leaving as new goals the subterms of `A` and `B` which are not definitionally equal. Example: suppose the goal is `x * f y = g w * f z`. Then congr will produce two goals: `x = g w` and `y = z`.

If `x y : t`, and an instance subsingleton t is in scope, then any goals of the form `x = y` are solved automatically.

The `congr` tactic, but takes an optional argument which gives
the depth of recursive applications.
* This is useful when `congr` without a depth bound is too aggressive in breaking down the goal.
* For example, given `⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
  and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`.
* If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.
-/
syntax (name := congrTactic) "congr" (ppSpace (colGt num))? : tactic
@[tactic congrTactic] def congrTacticImpl : Tactic := fun stx => 
match stx with
| `(tactic|congr $(x?)?) =>
  withMainContext do
    let x? := x?.map <| fun card => (Syntax.isNatLit? card).get!
    liftMetaTactic (Meta.congr x?)
| _ => throwIllFormedSyntax
-- TODO: use `congr' with p (: n)?` to call `ext p (: n)?` to all subgoals generated by `congr'`. For example, if the goal is `⊢ f '' s = g '' s` then `congr' with x` generates the goal
--   `x : α ⊢ f x = g x`.
-- this depends on `ext` implementing this case.

example (x y w: Nat)(f g: Nat → Nat): x * f y = g w * f z := by
  congr 
  have : x = g w := sorry
  assumption
  have : y = z := sorry
  assumption

example (x y : Nat)(f g: Nat → Nat): f (g (x + y)) = f (g (y + x)) := by
  congr 2
  have : x + y = y + x := sorry
  assumption

syntax "scowl" (ident)* : term
macro_rules
| `(scowl $[$xs]*) => `(sorry)

example : Nat := scowl very scowly  

example : String := scowl on the stealing of pens

def nn: MetaM Expr := do return ← mkArrow (mkConst ``Nat) (mkConst ``Nat)

open Expr

def target : Expr → Expr
  | Expr.lam n t b d => target b
  | Expr.forallE n t b d => target b
  | e => e

#check Term.elabTerm

def tst : TermElabM Expr := do
  let s ←  `(λ (x : Nat) => x + 2)
  let (e : Expr) ← Term.elabTerm s (Option.some (← mkArrow (mkConst ``Nat) (mkConst ``Nat)))
  let e ←  reduce e
  return (target e)

#eval tst

elab "tst!" : term => do
  tst

-- #eval tst!

-- For Metaprogramming in Lean

open Nat
def z' := mkConst `zero

#eval z'

def z := mkConst ``Nat.zero

#eval z

def one := mkApp (mkConst ``Nat.succ) z

#eval one

def natExp: Nat → Expr 
| 0 => z
| n + 1 => mkApp (mkConst ``Nat.succ) (natExp n)

#eval natExp 3

def sumExp : Nat → Nat → Expr 
| n, m => mkAppN (mkConst ``Nat.add) #[natExp n, natExp m]

#eval sumExp 2 3


def constZero : Expr := 
  mkLambda `cz BinderInfo.default  (mkConst ``Nat) (mkConst ``Nat.zero)
-- meta stuff

def double : MetaM Expr := do
  withLocalDecl `n BinderInfo.default (mkConst ``Nat)  fun n =>
    mkLambdaFVars #[n] <| mkAppN (mkConst ``Nat.add) #[n, n] 

#eval double

def sixExpr : MetaM Expr := do
  let expr := mkApp (← double) (natExp 3)
  let expr ← reduce expr
  return expr

#eval sixExpr

def zeroExpr : MetaM Expr := do
  let expr := mkApp constZero (natExp 3)
  let expr ← reduce expr
  return expr

#eval zeroExpr

#check @List.length

def lenExp (list: Expr) : MetaM Expr := do
  let expr ← mkAppM ``List.length #[list]
  let expr ← reduce expr
  return expr

def egList := [1, 3, 7, 8]

def egLen : MetaM Expr := 
  lenExp (mkConst ``egList)

#eval egLen


/-- natural number from expression built from `Nat.zero` and `Nat.succ` -/
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

def six : TermElabM Nat := do
  exprNat (← sixExpr)

#eval six

def eg: Option Nat := some 3

#eval eg.map (. * 2)
 
#eval OptionM.run do
    let x ← eg
    let y ← eg
    return x * 2 + y

def diff : (n: Nat) → (m: Nat) → m ≤ n → Nat 
| n, m, _ => n - m

macro n:term "--" m:term : term => 
  `(diff $n $m (by decide))

#eval 4 -- 3

def simpTheorems : CoreM SimpTheorems := getSimpTheorems
def simpLemmas : CoreM Nat := do
  let simpTheorems ← simpTheorems
  return simpTheorems.lemmaNames.size

#eval simpLemmas
#check simp
def simpCtx := Simp.Context.mkDefault

def simpLemmas2 : MetaM Nat := do
  let ctx ← simpCtx
  let simpTheorems := ctx.simpTheorems
  return simpTheorems.lemmaNames.size

#eval simpLemmas2

def simpDef(e: Expr) : MetaM Simp.Result := do simp e (← simpCtx)

elab "simp!" t:term: term => do 
  let e ← Term.elabTerm t none
  let r ← simpDef e
  return r.expr

#eval simp! 2

def addEg (x y: Nat) := simp! (Nat.add x (Nat.mul x y))

#print addEg

#check DiscrTree.mkPath