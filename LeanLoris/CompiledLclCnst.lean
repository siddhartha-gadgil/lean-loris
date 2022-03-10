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
open RecEvolverM

/-
Our main example of mixed reasoning is the result that if `f: Nat → α` is a function from natural numbers to a type `α` such that `∀ n : Nat, f (n + 1) = f n`, then `∀n : Nat, f n = f 0`, i.e. `f` is a constant function if it is locally constant.

We use two forms of backward reasoning: induction and introduction of variables based on goals (the latter can be replaced by forward reasoning). The forward reasoning we use is mainly function application and closure of equality under symmetry and transitivity. In the latter we implicitly use our key "lemma recognition" principle: proofs of simple statements are treated like simple terms while generating.
-/
namespace LclConst

constant α : Type
axiom a : α 
noncomputable instance : Inhabited α := ⟨a⟩
constant f : Nat → Nat 

-- the claims and proofs
def hyp! := ∀ n: Nat, f (n + 1) = f n
def claim! := ∀ n: Nat, f n = f 0
def baseclaim! := f 0 = f 0
def stepclaim! := ∀ n: Nat, f n = f 0 →  f (n + 1) = f 0
def base! := hyp! → baseclaim!
def step! := hyp! → stepclaim!
def recFn! := hyp! → baseclaim! → stepclaim! → claim!

def step : step! := fun h n ih => Eq.trans (h n) ih
def base : base! := fun _ => Eq.refl (f 0)
def recFn : recFn! := fun _  => natRec (fun n => f n = f 0)
def pf : hyp! → claim! := fun h => (recFn h) (base h) (step h)
def thm! := hyp! → claim!

-- running evolvers

def initData : FullData := (FinDist.empty, [], [])


-- the case that crashed

def goals0 : TermElabM (Array Expr) := do
                  parseExprArray (← 
                  `(expr_list|expr![thm!]))

def goals : TermElabM (Array Expr) := do
                  parseExprArray (← 
                  `(expr_list|expr![thm!, recFn!, base!, step!]))

-- #eval goals0

def init1 : TermElabM ExprDist := do
                  parseExprDist (← `(expr_dist|expr!{(thm!, 0)}))

def evolve1 : TermElabM EvolutionM := do
      let step := initEv ++ piGoals ++ rflEv ++ eqClosure ++ natRecEv ++ appl
      let ev := step.evolve.andThenM (logResults none <| ←  goals)
      return ev 2 (some 5000) initData

def evolve2 : TermElabM EvolutionM := do
      let step := initEv ++ piGoals ++ eqClosure
      let ev := step.evolve.andThenM (logResults none <| ←  goals)
      return ev 2 (some 5000) initData

def evolve0 : TermElabM EvolutionM := do
      let step := initEv ++ simpleApp
      let evBase := step.iterate.fixedPoint
      let ev := (evBase ^ (introEvolverM FullData false)) ++ evBase
      let ev := ev.andThenM (logResults none <| ←  goals)
      return ev 3 (some 500000) initData

def dist2 : TermElabM ExprDist := do
                  (← evolve1) * (← evolve2) <| (← init1)  

def view2 : TermElabM String := do
                  (← dist2).viewGoalsM (← goals)

def dist3 : TermElabM ExprDist := do
                  (← evolve1) * (← evolve1) * (← evolve0) <| 
                      (←  init1)  

def view3 : TermElabM String := do
              let res ← dist3
              res.viewGoalsM (← goals0)

def init0 : TermElabM ExprDist := do
                  parseExprDist (← `(expr_dist|expr!{(hyp! → claim!, 0), (base, 1), (recFn, 1), (step, 1)}))
-- #eval init0

def dist0 : TermElabM ExprDist := do
                  (← evolve0) (←  init0) 

def view0 : TermElabM String := do
                  (← dist0).viewGoalsM (← goals0)  
end LclConst