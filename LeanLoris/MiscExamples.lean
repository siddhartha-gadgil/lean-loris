import Lean.Meta
import Lean.Elab
import LeanLoris.Core
import LeanLoris.ProdSeq
import LeanLoris.Evolution
import LeanLoris.Syntax
import LeanLoris.TacticEvolution
import Std
open Std
open Lean Meta Elab Term
open ProdSeq

/- Examples for checking generation by combination rules, updating finite distributions, syntax for packing expressions, and evolution.-/

/- Generation and Evolution examples -/
def egEvolver : EvolverM Unit := 
  ((applyEvolver Unit).tautRec ++ (RecEvolverM.init Unit)).fixedPoint

def egEvolverFull : EvolverM FullData := 
  ((applyEvolver FullData).tautRec ++ (RecEvolverM.init FullData)).fixedPoint

elab "gen1!" t:term : term => do 
      let x ← elabTerm t none
      let l ← unpackWithDegree x
      let arr := l.toArray
      let m := FinDist.fromList l
      for (x, deg) in arr do
        logInfo m!"{x} : {deg}" 
      let m1 ← prodGenArrM  apply? 4 100 arr arr ()
      for (x, deg) in m1.allTermsArray do
        logInfo m!"{x} : {deg}" 
      let m2 ← egEvolver  4 100 () (← (ExprDist.fromArrayM arr)) 
      for (x, deg) in m2.allTermsArray do
        logInfo m!"{x} : {deg}" 
      logInfo "Evolved state"
      let m3 ← (egEvolver).evolve 12 100 () (← (ExprDist.fromArrayM arr))
      for (x, deg) in m3.allTermsArray do
        logInfo m!"{x} : {deg}" 
      logInfo "Full Evolved state"
      let m4 ← (egEvolverFull).evolve 12 100 (HashMap.empty, [], []) (← (ExprDist.fromArrayM arr)) 
                                          
      for (x, deg) in m4.allTermsArray do
        logInfo m!"{x} : {deg}" 
      return x

#check gen1! ((2, 1), (5, 2), (Nat.succ, 1), ())

/- Functions on finite distributions -/

def egMap := FinDist.fromList [(1, 2), (2, 3), (3, 4), (7, 1), (9, 1), (10, 3)]

#eval (egMap.degreeCount).toArray
#eval (egMap.cumulDegreeCount 6).toArray
#eval (egMap.filter (fun n => n % 2 = 1)).toArray
#eval (egMap.bound 2 10).toArray
#eval (egMap.bound 3 10).toArray
#eval (egMap.bound 3 4).toArray
#eval egMap.exists 6 6
#eval egMap.exists 10 2 -- not in dist because of the degree
#eval egMap.exists 10 3
#eval (FinDist.zeroLevel #[3, 4, 7]).toArray
#eval (FinDist.update egMap 10 4).getOp 10 -- not updated because of the degree
#eval (FinDist.update egMap 10 2).getOp 10
#eval (FinDist.update egMap 6 2).getOp 6


/- Evolution examples using Syntax -/
open Nat
def one := succ zero
def two := succ one

#check evolve! ev![app] expr![one, two] expr!{(succ, 0), (zero, 1)} name!{} 5 100 
#check evolve! ev![app] expr![one, two] expr!{(succ, 0), (zero, 1)} 5 100 
#check evolve! ev![app] expr!{(succ, 0), (zero, 1)}  5 100 

def eveg(α : Type):= fun (f g: α →  α) (a: α) => 
          evolve! ev![app] expr![f, f a, f (f a)] expr!{(a, 1), (f, 0), (g, 1)} 5 100
#reduce eveg


/- Using syntax and elaborators mixed with regular code -/

def syn: MacroM Syntax :=  `(evolver|app)
-- #check syn.run

def syn2: TermElabM Syntax :=  `(evolver_list|ev![app, name-app])
#check syn2.run

def lstfromsyn:  TermElabM (RecEvolverM FullData)  :=  do
        let syn ← syn2
        parseEvolverList syn

#check lstfromsyn

/- Packing and unpacking expression collections -/

elab (name:= exprDistPack) "packdist!" s:expr_dist : term => do
  let m : Array (Expr × Nat)  := (←  parseExprDist s).allTermsArray
  packWithDegree m.toList

#eval packdist! expr!{(1, 2), ("Hello", 4)}
#check packdist! expr!{(1, 2), ("Hello", 4)}

#reduce (fun x y : Nat => packdist! expr!{ (1, 2), ("Hello", 4), (x + 1 + y, 3)}) 4 7

elab (name:= exprPack) "pack!" s:expr_list : term => do
    let m : Array (Expr) ←  parseExprArray s
    pack m.toList

#check pack! expr![(1, 2), 3, ("Hello", 4), "over here"]

elab (name:= constpack) "const!" s:name_dist : term  => do
    let m : Array (Name × Nat) ←  parseNameMap s
    let c := m.map (fun (n, deg) => (mkConst n, deg))
    packWithDegree c.toList

elab (name := prodHead) "prodHead!" t:term : term => 
    do
      let expr ← elabTerm t none
      let h? ← splitPProd? expr 
      let hp? ← splitProd? expr
      match (h?.orElse (fun _ => hp?)) with
      | some (h, t) => return h
      | none => throwAbortTerm    

#eval prodHead! (10, 12, 15, 13)

elab "prodlHead!" t:term : term => 
    do
      let expr ← elabTerm t none
      let l ← try 
        unpack expr
        catch exc => throwError m!"Error {exc.toMessageData} while unpacking {expr}"
      return l.head!   

#eval prodlHead! (3, 10, 12, 13, ())

elab (name:= roundtrip) "roundtrip!" t:term : term => 
    do
      let expr ← elabTerm t none
      let l ← unpack expr
      let e ← pack l
      let ll ← unpack e
      let ee ← pack ll
      return ee

elab (name:= justterms) "terms!" t:term : term => 
    do
      let expr ← elabTerm t none
      let l ← unpack expr
      let e ← packTerms l
      return e

elab (name:= roundtripWtd) "roundtrip-(with degree)!" t:term : term =>
    do
      let expr ← elabTerm t none
      let l ← unpackWithDegree expr
      let e ← ppackWithDegree l
      let ll ← unpackWithDegree e
      let ee ← packWithDegree ll
      return ee

#eval roundtrip-(with degree)! (((), 9), (2, 7), ("Hello", 12), ())

/- "Tactic" evolution : recursion, meta to lambda etc -/

def egProp := ∀ n: Nat, n = n

def egFamily := natRecFamily <| mkConst `egProp

#eval egFamily


def sumEl : TermElabM Expr := do 
  let mvar1 ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvar2 ← mkFreshExprMVar (some (mkConst ``Nat)) -- none works too
  let value ← mkAppM ``Nat.add #[mvar1, mvar2]
  let mvar ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvarId := mvar.mvarId!
  assignExprMVar mvarId value
  metaToLambda [mvar1, mvar2] mvar

#eval sumEl

elab "sumEl!" : term => sumEl

#eval sumEl! 1 2

theorem constFn2{α : Type}(f: Nat → α):
    (∀ n : Nat, f n = f (n + 1)) →
    (∀ n : Nat, f n = f 0) := by
      intro hyp 
      apply natRec
      focus
        rfl
      focus
        intro n ih 
        rw [← hyp]
        assumption

def factorial : Nat →  Nat := by
  apply natRec
  focus
    exact 1
  focus
    intro n ih
    exact ((n + 1) * ih)

#eval factorial 5
