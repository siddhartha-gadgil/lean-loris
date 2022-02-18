import Lean.Meta
import Lean.Elab
open Lean Meta Elab Term
open Nat

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

  