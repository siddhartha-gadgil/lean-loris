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

set_option maxHeartbeats 100000000
set_option maxRecDepth 10000


def explore : TermElabM <| Array (String ×  Nat) := do
                  let lem1! := (m * n) * n = m 
                  let lem2! := (m * n) * ((m * n) * n) = n 
                  let lem3! := ((m * n) * m) * m = m * n
                  let ev0 ← parseEvolverList (← `(evolver_list|^[app, name-app, name-binop]))
                  let init0 ← parseExprMap (← `(expr_dist|%{(m, 0), (n, 0)}))
                  let goals0 ← parseExprList (← `(expr_list|%[m * n, m]))
                  let nameDist := #[(``mul, 0), (``ax1, 0), (``ax2, 0)]
                  let initData : FullData := (FinDist.fromArray nameDist, [], [])
                  let ev0 ← ev0.fixedPoint.evolve.andThenM (logResults goals0)
                  let dist1 ← ev0 2 1000 (← ExprDist.fromArray init0) initData
                  let reportDist ← goals0.filterMapM $ fun g => dist1.getTerm? g
                  let goals1 ← parseExprList (← `(expr_list|%[lem1!, lem2!, lem3!]))
                  let init1 ← parseExprMap (← `(expr_dist|%{(m, 0), (n, 0), (m *n, 0)}))
                  let ev1 ← parseEvolverList (← `(evolver_list|^[name-app, name-binop]))
                  let ev1 ← ev1.fixedPoint.evolve.andThenM (logResults goals1)
                  let dist2 ← ev1 3 1000 (← ExprDist.fromArray init1) initData
                  let reportDist ← goals1.filterMapM $ fun g => dist2.getProof? g
                  return reportDist.map <| fun (x, w) => (s!"{x}", w)
                  
-- #eval explore  

end ElabCzSl