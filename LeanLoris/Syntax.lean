import Lean
import Lean.Meta
import Lean.Elab
import LeanLoris.Evolution
import LeanLoris.ProdSeq
import LeanLoris.TacticEvolution
open Lean Elab Meta Term ProdSeq

declare_syntax_cat expr_dist 

syntax exprWt := "(" term "," num ")"
syntax exprWtList := "exp!{" exprWt,* "}"
syntax exprWtList : expr_dist
syntax "load:[" name "]" : expr_dist

def parseExprDist : Syntax → TermElabM ExprDist
  | `(expr_dist|exp!{$[$xs:exprWt],*}) =>
    do
          let m : Array (Expr × Nat) ←  xs.mapM (fun s => do
              match s with 
              | `(exprWt|($x:term , $n:numLit)) => 
                  let expr ← whnf <| ←  elabTerm x none
                  Term.synthesizeSyntheticMVarsNoPostponing
                  return (expr, (Syntax.isNatLit? n).get!)
              | _ =>
                throwError m!"{s} is not a valid exprWt"
              )
          ExprDist.fromArray m
  | `(expr_dist|load:[$x:nameLit]) =>
    do
      let name := x.getId
      ExprDist.load name
  | _ => throwIllFormedSyntax

elab (name:= exprDistPack) "packdist!" s:expr_dist : term => do
  let m : Array (Expr × Nat)  := (←  parseExprDist s).allTermsArr
  packWeighted m.toList


#eval packdist! exp!{(1, 2), ("Hello", 4)}
#check packdist! exp!{(1, 2), ("Hello", 4)}

#reduce (fun x y : Nat => packdist! exp!{ (1, 2), ("Hello", 4), (x + 1 + y, 3)}) 4 7

elab "find-proof!" p:term "in" d:expr_dist : term => do
  let dist ← parseExprDist d
  let prop ← elabType p
  let proofOpt ← dist.getProof? prop
  match proofOpt with
  | some (x, _) => return x
  | none => throwError "No proof found"

declare_syntax_cat expr_list
syntax "exp![" term,* "]" : expr_list

def parseExprArray : Syntax → TermElabM (Array Expr)
  | `(expr_list|exp![$[$xs],*]) =>
    do
          let m : Array Expr ←  xs.mapM <| fun s => 
            do 
              let exp ← elabTerm s none
              let exp ← whnf <| exp
              Term.synthesizeSyntheticMVarsNoPostponing
              return exp
          return m
  | _ => throwIllFormedSyntax

elab (name:= exprPack) "pack!" s:expr_list : term => do
    let m : Array (Expr) ←  parseExprArray s
    pack m.toList

#check pack! exp![(1, 2), 3, ("Hello", 4), "over here"]

declare_syntax_cat name_dist
syntax nameWt := "(" ident "," num ")"
syntax nameWtList := "name!{" nameWt,* "}"
syntax nameWtList : name_dist

def parseNameMap : Syntax → TermElabM (Array (Name × Nat))
  | `(name_dist|name!{$[$xs:nameWt],*}) =>
    do
          let m : Array (Name × Nat) ←  xs.mapM (fun s => do
              match s with 
              | `(nameWt|($x:ident, $n:numLit)) =>                  
                  return (x.getId, (Syntax.isNatLit? n).get!)
              | _ =>
                throwError m!"{s} is not a valid nameWt"
              )
          return m
  | _ => throwIllFormedSyntax

elab (name:= constpack) "const!" s:name_dist : term  => do
    let m : Array (Name × Nat) ←  parseNameMap s
    let c := m.map (fun (n, w) => (mkConst n, w))
    packWeighted c.toList


declare_syntax_cat evolver 
syntax "app" : evolver
syntax "name-app": evolver
syntax "binop": evolver
syntax "name-binop": evolver
syntax "simple-app": evolver
syntax "simple-binop": evolver
syntax "rewrite": evolver
syntax "rewrite-flip": evolver
syntax "congr": evolver
syntax "eq-isles": evolver
syntax "all-isles": evolver
syntax "func-dom-isles": evolver
syntax "eq-closure": evolver
syntax "eq-closure" (expr_list)?: evolver
syntax "pi-goals": evolver
syntax "pi-goals-all": evolver
syntax "rfl": evolver
syntax "nat-rec": evolver
syntax evolver "^" evolver : evolver

declare_syntax_cat evolve_transformer
syntax "by-type" (num)?: evolve_transformer

namespace RecEvolverM

abbrev appl := (applyEvolver FullData).tautRec
abbrev nameAppl := (nameApplyEvolver FullData).tautRec
abbrev binOp := (applyPairEvolver FullData).tautRec
abbrev nameBinOp := (nameApplyPairEvolver FullData).tautRec
abbrev simpleApp := (simpleApplyEvolver FullData).tautRec
abbrev simpleBinOp := (simpleApplyPairEvolver FullData).tautRec
abbrev rewriteEv := (rewriteEvolver FullData false).tautRec
abbrev rewriteFlip := (rewriteEvolver FullData true).tautRec
abbrev congrEv := (congrEvolver FullData).tautRec
abbrev eqIsles := eqIsleEvolver FullData
abbrev allIsles := allIsleEvolver FullData
abbrev funcDomIsles := funcDomIsleEvolver FullData
abbrev eqClosure := (eqSymmTransEvolver FullData).tautRec
abbrev piGoals := piGoalsEvolverM FullData 
abbrev rflEv := (rflEvolverM FullData).tautRec
abbrev natRecEv := (natRecEvolverM FullData).tautRec
abbrev initEv := init FullData

end RecEvolverM

declare_syntax_cat evolver_list
syntax "ev![" evolver,* (">>" evolve_transformer)? "]" : evolver_list
syntax "Σ" evolver_list : evolver

def parseEvolverTrans : Syntax → TermElabM (ExprDist → TermElabM ExprDist)
  | `(evolve_transformer|by-type) => return weightByType 1
  | `(evolve_transformer|by-type $n) => do
        let n ← parseNat n
        return weightByType n
  | stx => throwError m!"Evolver transformer not implemented for {stx}"


mutual
  partial def parseEvolver : Syntax → TermElabM (RecEvolverM FullData)
  | `(evolver|app) => return (applyEvolver FullData).tautRec
  | `(evolver|name-app) => return (nameApplyEvolver FullData).tautRec
  | `(evolver|binop) => return (applyPairEvolver FullData).tautRec
  | `(evolver|name-binop) => return (nameApplyPairEvolver FullData).tautRec
  | `(evolver|simple-app) => return (simpleApplyEvolver FullData).tautRec
  | `(evolver|simple-binop) => return (simpleApplyPairEvolver FullData).tautRec
  | `(evolver|rewrite) => return (rewriteEvolver FullData true).tautRec
  | `(evolver|rewrite-flip) => return (rewriteEvolver FullData false).tautRec
  | `(evolver|congr) => return (congrEvolver FullData).tautRec
  | `(evolver|eq-isles) => return eqIsleEvolver FullData
  | `(evolver|all-isles) => return allIsleEvolver FullData
  | `(evolver|func-dom-isles) => return funcDomIsleEvolver FullData
  | `(evolver|eq-closure) => return (eqSymmTransEvolver FullData).tautRec
  | `(evolver|eq-closure $goals) => do
          let goals ← parseExprArray goals
          return (eqSymmTransEvolver FullData goals).tautRec
  | `(evolver|pi-goals) => return piGoalsEvolverM FullData
  | `(evolver|pi-goals-all) => return piGoalsEvolverM FullData false
  | `(evolver|rfl) => return (rflEvolverM FullData).tautRec
  | `(evolver|nat-rec) => return (natRecEvolverM FullData).tautRec
  | `(evolver|$x:evolver ^ $y:evolver) => do
      let x ←  parseEvolver x
      let y ← parseEvolver y
      return (y.conjApply (x.fixedPoint)).tautRec
  | `(evolver|Σ $x) => parseEvolverList x
  | stx => throwError m!"Evolver not implemented for {stx}"

  partial def parseEvolverList : Syntax → TermElabM (RecEvolverM FullData)  
    | `(evolver_list|ev![$[$xs],*]) =>
      do
            let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
            return m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)
    | `(evolver_list|ev![$[$xs],* >> $tr]) =>
      do
            let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
            return (m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)).transformM 
                      <| ← parseEvolverTrans tr
    | _ => throwIllFormedSyntax
end

syntax save_target := "=:" name

syntax (name:= evolution) 
  "evolve!" evolver_list (expr_list)? expr_dist (name_dist)? num num (save_target)?  : term
@[termElab evolution] def evolutionImpl : TermElab := fun s _ =>
match s with
| `(evolve!%$tk $evolvers $(goals?)? $initDist $(nameDist?)? $wb $card $(saveTo?)?)  => do
  let ev ← parseEvolverList evolvers
  let initDist ← parseExprDist initDist
  let nameDist? ← nameDist?.mapM  $ fun nameDist => parseNameMap nameDist
  let nameDist := nameDist?.getD #[]
  let nameDist := FinDist.fromList (nameDist.toList)
  let initData : FullData := (nameDist, [], [])
  let goals? ← goals?.mapM $ fun goals => parseExprArray goals
  let goals := goals?.getD #[]
  let ev := ev.fixedPoint.evolve
  let saveTo? := saveTo?.bind <| fun stx =>
    match stx with  
    | `(save_target|=:$x) => some x.getId
    | _ => none
  let wb ← parseNat wb
  let card ← parseNat card
  let finalDist ← ev wb card initData initDist 
  match saveTo? with
  | some name => ExprDist.save name finalDist
  | none => pure ()
  logResults (some tk) goals finalDist
  let reportDist ← goals.mapM $ fun g => do
    let pfOpt ←  (finalDist.getProof? g)
    return pfOpt.getD (mkConst ``Unit, 0)
  return ← (ppackWeighted reportDist.toList)
| _ => throwIllFormedSyntax

def syn: MacroM Syntax :=  `(evolver|app)
-- #check syn.run

def syn2: TermElabM Syntax :=  `(evolver_list|ev![app, name-app])
-- #check syn2.run
def lstfromsyn:  TermElabM (RecEvolverM FullData)  :=  do
        let syn ← syn2
        parseEvolverList syn

-- #check lstfromsyn

elab "hash!" t:term : term => do
    let expr ← elabTerm t none
    let expr ← whnf expr
    let h ← exprHash expr
    let n := h.toNat
    logInfo m!"expr: {expr}"
    logInfo m!"hash: {n}"
    return ToExpr.toExpr n

elab "hashv!" t:term : term => do
    let expr ← elabTerm t none
    let expr ← whnf expr
    let h ← exprHashV expr
    let n := h.toNat
    logInfo m!"expr: {expr}"
    logInfo m!"hash: {n}"
    return ToExpr.toExpr n

#check (3 : UInt64).toNat