import Lean.Meta
import Lean.Elab
import LeanLoris.Core
import LeanLoris.ProdSeq
import LeanLoris.Evolution
open Lean Meta Elab Term
open ProdSeq

syntax (name:=genOne) "gen1!" term : term
@[termElab genOne] def gen1Impl : TermElab
  | stx, _ => 
  match stx with
    | `(gen1! $t) => do 
      let x ← elabTerm t none
      let l ← unpackWeighted x
      let m := FinDist.fromList l
      for (x, w) in m.toArray do
        logInfo m!"{x} : {w}" 
      let m1 ← prodGenM  applyOpt 4 100 m m (fun _ _ _ _ => true)
      for (x, w) in m1.toArray do
        logInfo m!"{x} : {w}" 
      let m2 ← egEvolver  4 100 m ()
      for (x, w) in m2.toArray do
        logInfo m!"{x} : {w}" 
      logInfo "Evolved state"
      let m3 ← (egEvolver).evolve 12 100 m ()
      for (x, w) in m3.toArray do
        logInfo m!"{x} : {w}" 
      return x
    | _ => throwIllFormedSyntax

#check gen1! ((2, 1), (5, 2), (Nat.succ, 1), ())

def egMap := FinDist.fromList [(1, 2), (2, 3), (3, 4), (7, 1), (9, 1), (10, 3)]

-- tests for helpers

#eval (egMap.weightCount).toArray

#eval (egMap.cumulWeightCount).toArray

#eval (egMap.filter (fun n => n % 2 = 1)).toArray

#eval (egMap.bound 2 10).toArray

#eval (egMap.bound 3 10).toArray

#eval (egMap.bound 3 4).toArray

#eval egMap.exists 6 6

#eval egMap.exists 10 2 -- not in dist because of the weight

#eval egMap.exists 10 3

#eval (FinDist.zeroLevel #[3, 4, 7]).toArray

#eval (FinDist.update egMap 10 4).getOp 10 -- not updated because of the weight

#eval (FinDist.update egMap 10 2).getOp 10

#eval (FinDist.update egMap 6 2).getOp 6