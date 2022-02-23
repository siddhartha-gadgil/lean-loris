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

namespace RecEg

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
                  parseExprList (← 
                  `(expr_list|%[thm!]))

def goals : TermElabM (Array Expr) := do
                  parseExprList (← 
                  `(expr_list|%[thm!, recFn!, base!, step!]))

-- #eval goals0

def init1 : TermElabM (Array (Expr × Nat)) := do
                  parseExprMap (← `(expr_dist|%{(thm!, 0)}))

def evolve1 : TermElabM EvolutionM := do
      let step ← parseEvolverList (← 
                  `(evolver_list|^[pi-goals, rfl, eq-closure, nat-rec, app]))
      let ev := step.fixedPoint.evolve.andThenM (logResults <| ←  goals)
      return ev 2 5000 initData

def evolve2 : TermElabM EvolutionM := do
      let step ← parseEvolverList (← 
                  `(evolver_list|^[pi-goals, eq-closure]))
      let ev := step.fixedPoint.evolve.andThenM (logResults <| ←  goals)
      return ev 2 5000 initData

def evolve0 : TermElabM EvolutionM := do
      let step ← parseEvolverList (← 
                  `(evolver_list|^[simple-app]))
      let evBase := step.iterate.fixedPoint.andThenM (logResults <| ←  goals)
      let ev := (evBase ^ (piGoalsEvolverM FullData false)) ++ evBase
      return ev 3 500000 initData

def dist2 : TermElabM ExprDist := do
                  (← evolve1) * (← evolve2) <| (← ExprDist.fromArray <| ←  init1)  

def view2 : TermElabM String := do
                  (← dist2).viewGoals (← goals)

def dist3 : TermElabM ExprDist := do
                  (← evolve1) * (← evolve1) * (← evolve0) <| 
                      (← ExprDist.fromArray <| ←  init1)  

def view3 : TermElabM String := do
                  (← dist3).viewGoals (← goals)

def init0 : TermElabM (Array (Expr × Nat)) := do
                  parseExprMap (← `(expr_dist|%{(hyp! → claim!, 0), (base, 1), (recFn, 1), (step, 1)}))
-- #eval init0

def dist0 : TermElabM ExprDist := do
                  (← evolve0) (← ExprDist.fromArray <| ←  init0) 

def view0 : TermElabM String := do
                  (← dist0).viewGoals (← goals0)  
end RecEg