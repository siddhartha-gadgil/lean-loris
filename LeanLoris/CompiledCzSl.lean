import LeanLoris.Evolution
import LeanLoris.FinDist
import LeanLoris.ExprDist
import LeanLoris.Core
import LeanLoris.ProdSeq
import LeanLoris.Syntax
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
open ProdSeq
open RecEvolverM

namespace CzSl
constant M : Type

instance : Inhabited (M → M → M) := ⟨fun x _ => x⟩

constant mul : M → M → M


noncomputable instance : Mul M := ⟨mul⟩

@[simp] theorem mul_eq(a b : M) : mul a b = a * b := by rfl

axiom ax1 : (∀ a b : M, (a * b) * b = a)
axiom ax2 : (∀ a b : M, a * (a * b) = b)
axiom m : M
axiom n : M

/--
Our main model problem for forward reasoning is the following from a Czech-Slovak Olympiad:

Let `M` be a set with a product. Given the axioms:
* `∀ a b : M, (a * b) * b = a`
* `∀ a b : M, a * (a * b) = b`
then, for arbitrary elements `m` and `n` in `M`, we have `m * n = n * m`.

We fix `m` and `n` and reason forward starting with `m`, `n`, the axioms, and multiplication. Our forward reasoning is tuned for this problem, and also mildly help by including `m *n` in the initial state. But we do not use the statement of the problem, any of the lemmas or the proof.

To understand the (automated) reasoning steps (and for use during tuning and debugging), some lemmas and the theorem were defined. While running progress in proving these is logged.

* `def lem1! := (m * n) * n = m` 
* `def lem2! := (m * n) * ((m * n) * n) = n`
* `def lem3! := ((m * n) * m) * m = m * n`
* `def lem4! := (m * n) * ((m * n) * n) = (m * n) * m`
* `def lem5! := (m * n) * m = n`
* `def lem6! := ((m * n) * m) * m = n * m`
* `def thm! := m * n = n * m`

The `view4` function below is run in the `Main` module and its result is output (as are indicators of progress in intermediate steps).

The forward reasoning we use is mainly function application and closure of equality under symmetry and transitivity. In the latter we implicitly use our key "lemma recognition" principle: proofs of simple statements are treated like simple terms while generating.
-/
theorem CzSlOly : m * n = n * m := by
              have lem1 : (m * n) * n = m := ax1 m n
              have lem2 : (m * n) * ((m * n) * n) = n := ax2 (m * n) n
              have lem3 : ((m * n) * m) * m = m * n  := ax1 (m * n) m
              have lem4 : (m * n) * ((m * n) * n) = (m * n) * m := 
                  congrArg (fun x => (m * n) * x) lem1              
              have lem5 : (m * n) * m = n := by
                    rw [lem4] at lem2
                    assumption
              have lem6 : ((m * n) * m) * m = n * m  := 
                    congrArg (fun x => x * m) lem5 
              rw [lem3] at lem6
              assumption 

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000

def lem1! := (m * n) * n = m 
def lem2! := (m * n) * ((m * n) * n) = n
def lem3! := ((m * n) * m) * m = m * n
def lem4! := (m * n) * ((m * n) * n) = (m * n) * m
def lem5! := (m * n) * m = n
def lem6! := ((m * n) * m) * m = n * m
def thm! := m * n = n * m

def nameDist := #[(``mul, 0), (``ax1, 0), (``ax2, 0)]

def init1 : TermElabM ExprDist := do
                  parseExprDist (← `(expr_dist|expr!{(m, 0), (n, 0), (m *n, 0)}))

def initData : FullData := (FinDist.fromArray nameDist, [], [])

def goals : TermElabM (Array Expr) := do
                  parseExprArray (← 
                  `(expr_list|expr![lem1!, lem2!, lem3!, lem4!, lem5!, lem6!, thm!]))

def evolve1: TermElabM EvolutionM := do
            let step := initEv ++ nameAppl ++ nameBinOp ++ eqIsles
            let ev  := step.evolve.andThenM (logResults none <| ←  goals)
            return ev 3 (some 6000) initData

def evolve2: TermElabM EvolutionM := do
            let step := initEv ++ eqClosure
            let ev  := step.evolve.andThenM (logResults none <| ←  goals)
            return ev 1 (some 6000) initData

def evolve : TermElabM EvolutionM := do
      return (← evolve1) * (← evolve2) * (← evolve1) * (← evolve2)

def goals4 : TermElabM (Array Expr) := do
                  parseExprArray (← `(expr_list|expr![thm!]))
def dist4 : TermElabM ExprDist := do
                  (← evolve) (←  init1) 

def view4 : TermElabM String := do
                  (← dist4).viewGoalsM (← goals4)                

#check @mul
#check @HMul.hMul

end CzSl
