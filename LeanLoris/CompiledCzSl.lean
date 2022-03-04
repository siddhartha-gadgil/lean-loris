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
def lem6! := ((m * n) * m) * m = n * m
def thm! := m * n = n * m

def nameDist := #[(``mul, 0), (``ax1, 0), (``ax2, 0)]
def initData : FullData := (FinDist.fromArray nameDist, [], [])

def goals : TermElabM (Array Expr) := do
                  parseExprArray (← 
                  `(expr_list|exp![lem1!, lem2!, lem3!, lem4!, lem5!, lem6!, thm!]))

def evolve1: TermElabM EvolutionM := do
            let step := initEv ++ nameAppl ++ nameBinOp ++ eqIsles
            let ev  := step.evolve.andThenM (logResults none <| ←  goals)
            return ev 3 6000 initData

def evolve2: TermElabM EvolutionM := do
            let step := initEv ++ eqClosure
            let ev  := step.evolve.andThenM (logResults none <| ←  goals)
            return ev 1 6000 initData

def evolve : TermElabM EvolutionM := do
      return (← evolve1) * (← evolve2) * (← evolve1) * (← evolve2)

def init1 : TermElabM ExprDist := do
                  parseExprDist (← `(expr_dist|exp!{(m, 0), (n, 0), (m *n, 0)}))

def goals4 : TermElabM (Array Expr) := do
                  parseExprArray (← `(expr_list|exp![thm!]))
def dist4 : TermElabM ExprDist := do
                  (← evolve) (←  init1) 

def view4 : TermElabM String := do
                  (← dist4).viewGoals (← goals4)                

#check @mul
#check @HMul.hMul

end CzSl
