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
                  parseExprArray (← 
                  `(expr_list|exp![thm!]))

def goals : TermElabM (Array Expr) := do
                  parseExprArray (← 
                  `(expr_list|exp![thm!, recFn!, base!, step!]))

-- #eval goals0

def init1 : TermElabM ExprDist := do
                  parseExprDist (← `(expr_dist|exp!{(thm!, 0)}))

def evolve1 : TermElabM EvolutionM := do
      let step := initEv ++ piGoals ++ rflEv ++ eqClosure ++ natRecEv ++ appl
      let ev := step.evolve.andThenM (logResults none <| ←  goals)
      return ev 2 5000 initData

def evolve2 : TermElabM EvolutionM := do
      let step := initEv ++ piGoals ++ eqClosure
      let ev := step.evolve.andThenM (logResults none <| ←  goals)
      return ev 2 5000 initData

def evolve0 : TermElabM EvolutionM := do
      let step := initEv ++ simpleApp
      let evBase := step.iterate.fixedPoint
      let ev := (evBase ^ (piGoalsEvolverM FullData false)) ++ evBase
      let ev := ev.andThenM (logResults none <| ←  goals)
      return ev 3 500000 initData

def dist2 : TermElabM ExprDist := do
                  (← evolve1) * (← evolve2) <| (← init1)  

def view2 : TermElabM String := do
                  (← dist2).viewGoals (← goals)

def dist3 : TermElabM ExprDist := do
                  (← evolve1) * (← evolve1) * (← evolve0) <| 
                      (←  init1)  

def view3 : TermElabM String := do
              let res ← dist3
              ExprDist.save `dist3 res
              let loaded ← ExprDist.load `dist3
              IO.println s!"saved and loaded; terms: {loaded.termsArr.size}, proofs: {loaded.proofsArr.size}"
              loaded.viewGoals (← goals)

def init0 : TermElabM ExprDist := do
                  parseExprDist (← `(expr_dist|exp!{(hyp! → claim!, 0), (base, 1), (recFn, 1), (step, 1)}))
-- #eval init0

def dist0 : TermElabM ExprDist := do
                  (← evolve0) (←  init0) 

def view0 : TermElabM String := do
                  (← dist0).viewGoals (← goals0)  
end RecEg