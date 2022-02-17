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

def evStep1 : TermElabM (RecEvolverM FullData) := do
                  parseEvolverList (← 
                  `(evolver_list|^[pi-goals, rfl, eq-closure, nat-rec, app]))


def ev1 : TermElabM (EvolverM FullData) := do
                  return (← evStep1).fixedPoint.evolve.andThenM (logResults <| ←  goals) 

def dist1 : TermElabM ExprDist := do
                  (← ev1) 2 5000 initData (← ExprDist.fromArray <| ←  init1) 

def view1 : TermElabM String := do
                  (← dist1).viewGoals (← goals) 

def evStep2 : TermElabM (RecEvolverM FullData) := do
                  parseEvolverList (← 
                  `(evolver_list|^[pi-goals, eq-closure]))


def ev2 : TermElabM (EvolverM FullData) := do
                  return (← evStep2).fixedPoint.evolve.andThenM (logResults <| ←  goals) 

def dist2 : TermElabM ExprDist := do
                  (← ev2) 2 5000 initData (← dist1) 

def view2 : TermElabM String := do
                  (← dist2).viewGoals (← goals)

def init0 : TermElabM (Array (Expr × Nat)) := do
                  parseExprMap (← `(expr_dist|%{(hyp! → claim!, 0), (base, 0), (recFn, 0), (step, 1)}))
-- #eval init0


def evStep0 : TermElabM (RecEvolverM FullData) := do
                  parseEvolverList (← `(evolver_list|^[pi-goals, simple-binop]))

-- #check evStep0

def ev0 : TermElabM (EvolverM FullData) := do
                  return (← evStep0).fixedPoint.evolve

def dist0 : TermElabM ExprDist := do
                  (← ev0) 2 50000 initData (← ExprDist.fromArray <| ←  init0) 

def view0 : TermElabM String := do
                  (← dist0).viewGoals (← goals0)  
end RecEg