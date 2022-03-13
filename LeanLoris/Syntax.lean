import Lean
import Lean.Meta
import Lean.Elab
import LeanLoris.Evolution
import LeanLoris.ProdSeq
import LeanLoris.TacticEvolution
open Lean Elab Meta Term ProdSeq

/- 
Syntax categories, definitions, elaborators and parsers. The main role of these is to allow expressions to be extracted and passed as arguments to the evolution functions.

There are also functions, both ordinary and meta, as notation.
-/

/--
Parsing a natural number, assuming that the expression obtained by elaboration and taking normal form is built from `Nat.zero` and `Nat.succ`.
-/
def parseNat : Syntax → TermElabM Nat := fun s => 
  do
    let expr ← elabTerm s none
    exprNat expr

/- 
Syntax and elaborators for arrays of expressions with degrees; parsed to `ExprDist`. A saved `ExprDist` is specified by its identifier.
-/

declare_syntax_cat expr_dist 

syntax exprWt := "(" term "," term ")"
syntax exprWtList := "expr!{" exprWt,* "}"
syntax exprWtList : expr_dist
syntax ident : expr_dist

/-- `ExprDist` from syntax for a list of expressions with degrees -/
def parseExprDist : Syntax → TermElabM ExprDist
  | `(expr_dist|expr!{$[$xs:exprWt],*}) =>
    do
          let m : Array (Expr × Nat) ←  xs.mapM (fun s => do
              match s with 
              | `(exprWt|($x:term , $n:term)) => 
                  let expr ← whnf <| ← reduce <| ←  elabTerm x none
                  Term.synthesizeSyntheticMVarsNoPostponing
                  return (expr, (Syntax.isNatLit? n).get!)
              | _ =>
                throwError m!"{s} is not a valid exprWt"
              )
          ExprDist.fromArrayM m
  | `(expr_dist|$x:ident) =>
    do
      let name := x.getId
      ExprDist.load name
  | _ => throwIllFormedSyntax

-- finding a proof in an `ExprDist`
elab "find-proof!" p:term "in" d:expr_dist : term => do
  let dist ← parseExprDist d
  let prop ← elabType p
  let proof? ← dist.getProofM? prop
  match proof? with
  | some (x, _) => return x
  | none => throwError "No proof found"

/- Lists of expressions from Syntax -/
declare_syntax_cat expr_list
syntax "expr![" term,* "]" : expr_list

/-- List of expressions parsed from syntax -/
def parseExprArray : Syntax → TermElabM (Array Expr)
  | `(expr_list|expr![$[$xs],*]) =>
    do
          let m : Array Expr ←  xs.mapM <| fun s => 
            do 
              let exp ← elabTerm s none
              let exp ← whnf <| exp
              Term.synthesizeSyntheticMVarsNoPostponing
              return exp
          return m
  | _ => throwIllFormedSyntax

/- Distributions of names from syntax -/
declare_syntax_cat name_dist
syntax nameWt := "(" ident "," num ")"
syntax nameWtList := "name!{" nameWt,* "}"
syntax nameWtList : name_dist

/-- Distribution of names parsed from syntax-/
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

/- Syntax for an evolver -/
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
syntax "congr-rec": evolver
syntax "all-isles": evolver
syntax "func-dom-isles": evolver
syntax "eq-closure": evolver
syntax "eq-closure" (expr_list)?: evolver
syntax "intro": evolver
syntax "intro-all": evolver
syntax "rfl": evolver
syntax "nat-rec": evolver
syntax evolver "^" evolver : evolver
syntax evolver "^" "+" evolver : evolver

declare_syntax_cat evolve_transformer
syntax "by-type" (num)?: evolve_transformer

/- Shorter names for evolvers, close to the syntax versions -/
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
abbrev eqIsles := congrIsleEvolver FullData
abbrev allIsles := allIsleEvolver FullData
abbrev funcDomIsles := funcDomIsleEvolver FullData
abbrev eqClosure := (eqSymmTransEvolver FullData).tautRec
abbrev introEv := introEvolverM FullData 
abbrev rflEv := (rflEvolverM FullData).tautRec
abbrev natRecEv := (natRecEvolverM FullData).tautRec
abbrev initEv := init FullData

end RecEvolverM

/- Syntax for a list of evolvers, possibly with transformation -/
declare_syntax_cat evolver_list
syntax "ev![" evolver,* (">>" evolve_transformer)? "]" : evolver_list
syntax "Σ" evolver_list : evolver

/-- Evolver transformer parsed from syntax -/
def parseEvolverTransformer : Syntax → TermElabM (ExprDist → TermElabM ExprDist)
  | `(evolve_transformer|by-type) => return degreeByType 1
  | `(evolve_transformer|by-type $n) => do
        let n ← parseNat n
        return degreeByType n
  | stx => throwError m!"Evolver transformer not implemented for {stx}"

mutual
  /-- Evolver parsed from syntax -/
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
  | `(evolver|congr-rec) => return congrIsleEvolver FullData
  | `(evolver|all-isles) => return allIsleEvolver FullData
  | `(evolver|func-dom-isles) => return funcDomIsleEvolver FullData
  | `(evolver|eq-closure) => return (eqSymmTransEvolver FullData).tautRec
  | `(evolver|eq-closure $goals) => do
          let goals ← parseExprArray goals
          return (eqSymmTransEvolver FullData goals).tautRec
  | `(evolver|intro) => return introEvolverM FullData
  | `(evolver|intro-all) => return introEvolverM FullData false
  | `(evolver|rfl) => return (rflEvolverM FullData).tautRec
  | `(evolver|nat-rec) => return (natRecEvolverM FullData).tautRec
  | `(evolver|$x:evolver ^ $y:evolver) => do
      let x ←  parseEvolver x
      let y ← parseEvolver y
      return (y.conjApply (x.fixedPoint)).tautRec
  | `(evolver|$x:evolver ^+ $y:evolver) => do
      let x ←  parseEvolver x
      let x := (RecEvolverM.init FullData) ++ x
      let y ← parseEvolver y
      return (y.conjApply (x.fixedPoint)).tautRec
  | `(evolver|Σ $x) => parseEvolverList x
  | stx => throwError m!"Evolver not implemented for {stx}"

  /-- List of evolvers parsed from syntax and folded. The initial evolver is automatically included. -/
  partial def parseEvolverList : Syntax → TermElabM (RecEvolverM FullData)  
    | `(evolver_list|ev![$[$xs],*]) =>
      do
            let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
            return m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)
    | `(evolver_list|ev![$[$xs],* >> $tr]) =>
      do
            let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
            return (m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)).transformM 
                      <| ← parseEvolverTransformer tr
    | _ => throwIllFormedSyntax
end

/- Syntax and elaboration for evolution determined by evolvers and parameters-/
syntax save_target := "=:" ident

syntax (name:= evolution) 
  "evolve!" evolver_list (expr_list)? expr_dist (name_dist)? num (num)? (save_target)?  : term
@[termElab evolution] def evolutionImpl : TermElab := fun s _ =>
match s with
| `(evolve!%$tk $evolvers $(goals?)? $initDist $(nameDist?)? $degBnd $(card?)? $(saveTo?)?)  => do
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
  let degBnd ← parseNat degBnd
  let card := card?.map <| fun card => (Syntax.isNatLit? card).get!
  let finalDist ← ev degBnd card initData initDist 
  match saveTo? with
  | some name => ExprDist.save name finalDist
  | none => pure ()
  logResults (some tk) goals finalDist
  let reportDist ← goals.mapM $ fun g => do
    let pf? ←  (finalDist.getProofM? g)
    return pf?.getD (mkConst ``Unit, 0)
  return ← (ppackWithDegree reportDist.toList)
| _ => throwIllFormedSyntax


-- generating expression hashes; created for debugging
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

/- Evolution as a tactic -/

open Lean.Elab.Tactic

syntax (name:= evolveTactic) 
  "evolve" evolver_list (expr_list)? (expr_dist)? (name_dist)? num (num)? (save_target)?  : tactic
@[tactic evolveTactic] def evolveImpl : Tactic := fun stx =>
match stx with
| `(tactic|evolve%$tk $evolvers $(goals?)? $(initDist?)? $(nameDist?)? $degBnd $(card?)? $(saveTo?)?)  => 
  withMainContext do
  let ev ← parseEvolverList evolvers
  let lctx ← getLCtx
  let fvars := 
    lctx.decls.toList.filterMap (fun  decl? => 
    match decl? with
      | some decl => if !decl.isLet then 
        some <| mkFVar decl.fvarId 
        else none
      | none      => none)
  let fvars := fvars.tail!
  let initDist ← match initDist? with
    | some initDist => parseExprDist initDist
    | none => 
        let initTerms := fvars.toArray 
        let target ← getMainTarget
        let initTerms:= initTerms.push target
        ExprDist.fromArrayM (initTerms.map fun fvar => (fvar, 0))
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
  let degBnd ← parseNat degBnd
  let card := card?.map <| fun card => (Syntax.isNatLit? card).get!
  let finalDist ← ev degBnd card initData initDist 
  match saveTo? with
  | some name => ExprDist.save name finalDist
  | none => pure ()
  logResults (some tk) goals finalDist
  match ← finalDist.getProofM? (← getMainTarget) with
  | some (pf, _) => 
      assignExprMVar (← getMainGoal) pf
      replaceMainGoal []
  | none => 
      pure () 
  return ()
| _ => throwIllFormedSyntax
