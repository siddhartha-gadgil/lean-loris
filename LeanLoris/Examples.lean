import Lean.Meta
import Lean.Elab
import LeanLoris.Core
import LeanLoris.ProdSeq
open Lean Meta Elab Term
open ProdSeq

syntax (name:=genOne) "gen1!" term : term
@[termElab genOne] def gen1Impl : TermElab
  | stx, _ => 
  match stx with
    | `(gen1! $t) => do 
      let x ← elabTerm t none
      let l ← unpackWeighted x
      let m := mapFromList l
      for (x, w) in m.toArray do
        logInfo m!"{x} : {w}" 
      let m1 ← prodGenM  applyOpt 4 100 m m
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