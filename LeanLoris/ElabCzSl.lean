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
                  let nameDist := #[(``mul, 0)]
                  let initData : FullData := (FinDist.fromArray nameDist, [], [])
                  let ev0 ← ev0.fixedPoint.evolve.andThenM (logResults goals0)
                  let finalDist ← ev0 2 1000 (← ExprDist.fromArray init0) initData
                  let reportDist ← goals0.filterMapM $ fun g => finalDist.getTerm? g
                  return reportDist.map <| fun (x, w) => (s!"{x}", w)

#eval explore  

syntax (name:=mulmn) "ml!" "(" term "," term ")"  : term
@[termElab mulmn] def mulmnImpl : TermElab := 
      fun stx _ => do
      match stx with
      | `(ml! ($x, $y)) => do
        let m ← elabTerm x none
        let n ← elabTerm y none
        let e ← mkAppM ``mul #[m , n]
        return e
      | _ => throwIllFormedSyntax

#check ml! (m, n)

end ElabCzSl