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

universe u

variable {M: Type u}[Mul M]

theorem CzSlOly : (∀ a b : M, (a * b) * b = a) → (∀ a b : M, a * (a * b) = b) →
            (m n: M) → m * n = n * m := by
              intros ax1 ax2 m n
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

set_option maxHeartbeats 100000000

def mul(m n: M) : M := m * n

def explore(ax1 : ∀ a b : M, (a * b) * b = a)(ax2 : ∀ a b : M, a * (a * b) = b)
                  (m n: M) : TermElabM Nat := do
                  let lem1! := (m * n) * n = m 
                  let lem2! := (m * n) * ((m * n) * n) = n 
                  let lem3! := ((m * n) * m) * m = m * n
                  let ev0 ← parseEvolverList (← `(evolver_list|^[app, name-app]))
                  let init0 ← parseExprMap (← `(expr_dist|%{(m, 0), (n, 0)}))
                  let goals ← parseExprList (← `(expr_list|%[m* n]))
                  let nameDist ← parseNameMap (← `(name_dist|!{(mul, 0)}))
                  let initData : FullData := (FinDist.fromArray nameDist, [], [])
                  let ev0 ← ev0.fixedPoint.evolve.andThenM (logResults goals)
                  let finalDist ← ev0 5 1000 (← ExprDist.fromTermsM (FinDist.fromArray init0)) initData
                  let reportDist ← goals.filterMapM $ fun g => finalDist.getProof? g
                  let pp ← (ppackWeighted reportDist.toList)
                  return reportDist.size

#check explore

end ElabCzSl