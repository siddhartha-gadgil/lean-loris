import LeanLoris.Evolution
import LeanLoris.FinDist
import LeanLoris.ExprDist
import LeanLoris.Core
import LeanLoris.ProdSeq
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

namespace ElabCzSl
constant M : Type

instance : Inhabited (M → M → M) := ⟨fun x _ => x⟩

constant mul : M → M → M


noncomputable instance : Mul M := ⟨mul⟩

axiom ax1 : (∀ a b : M, (a * b) * b = a)
axiom ax2 : (∀ a b : M, a * (a * b) = b)
axiom m : M
axiom n : M


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
def evr0 : TermElabM (RecEvolverM FullData) := do
                  parseEvolverList (← `(evolver_list|^[name-app, name-binop]))
def init0 : TermElabM (Array (Expr × Nat)) := do
                  parseExprMap (← `(expr_dist|%{(m, 0), (n, 0)}))
def goals0 : TermElabM (Array Expr) := do
                  parseExprList (← `(expr_list|%[m * n, m]))
#eval init0
def nameDist := #[(``mul, 0), (``ax1, 0), (``ax2, 0)]
def initData : FullData := (FinDist.fromArray nameDist, [], [])
def ev0 : TermElabM (EvolutionM FullData) := do
                  (← evr0).fixedPoint.evolve.andThenM (logResults <| ←  goals0)
def fin0 : TermElabM ExprDist := do
                  (← ev0) 2 1000 (← ExprDist.fromArray <| ←  init0) initData
def rep0 : TermElabM (Array (Expr × Nat)) := do
                  (← fin0).getGoals (← goals0)
#eval rep0

def goals1 : TermElabM (Array Expr) := do
                  parseExprList (← `(expr_list|%[lem1!, lem2!, lem3!]))
#eval goals1
def init1 : TermElabM (Array (Expr × Nat)) := do
                  parseExprMap (← `(expr_dist|%{(m, 0), (n, 0), (m *n, 0)}))
def evr1 : TermElabM (RecEvolverM FullData) := do
                  parseEvolverList (← `(evolver_list|^[name-app, name-binop]))                  
def ev1 : TermElabM (EvolutionM FullData) := do
                  (← evr1).fixedPoint.evolve.andThenM (logResults <| ←  goals1)
def fin1 : TermElabM ExprDist := do
                  (← ev1) 3 1000 (← ExprDist.fromArray <| ←  init1) initData
def rep1 : TermElabM (Array (Expr × Nat)) := do
                  (← fin1).getGoals (← goals1)

#eval rep1


end ElabCzSl