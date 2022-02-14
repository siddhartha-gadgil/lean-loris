import Lean
import Lean.Meta
import Lean.Elab
import LeanLoris.Evolution
import LeanLoris.ProdSeq
open Lean Elab Meta Term ProdSeq

declare_syntax_cat expr_dist 

syntax exprWt := "(" term "," num ")"
syntax exprWtList := "%{" exprWt,* "}"
syntax exprWtList : expr_dist

def parseExprMap : Syntax → TermElabM (Array (Expr × Nat))
  | `(expr_dist|%{$[$xs:exprWt],*}) =>
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
          m
  | _ => throwIllFormedSyntax

syntax (name:= exprDistPack) "packdist!" expr_dist : term
@[termElab exprDistPack] def exprDistPackImpl : TermElab := fun stx _ =>
    match stx with 
    | `(packdist! $s:expr_dist) => 
        do
          let m : Array (Expr × Nat) ←  parseExprMap s
          packWeighted m.toList
    | _ => throwIllFormedSyntax

-- #eval packdist! %{(1, 2), ("Hello", 4)}
-- #check packdist! %{(1, 2), ("Hello", 4)}

#reduce (fun x y : Nat => packdist!%{ (1, 2), ("Hello", 4), (x + 1 + y, 3)}) 4 7

declare_syntax_cat expr_list
syntax "%[" term,* "]" : expr_list

def parseExprList : Syntax → TermElabM (Array Expr)
  | `(expr_list|%[$[$xs],*]) =>
    do
          let m : Array Expr ←  xs.mapM <| fun s => 
            do 
              let exp ← elabTerm s none
              let exp ← whnf <| exp
              Term.synthesizeSyntheticMVarsNoPostponing
              exp
          return m
  | _ => throwIllFormedSyntax

syntax (name:= exprPack) "pack!" expr_list : term
@[termElab exprPack] def exprPackImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(pack! $s:expr_list) => 
    do
          let m : Array (Expr) ←  parseExprList s
          pack m.toList
  | _ => throwIllFormedSyntax

-- #check pack! %[(1, 2), 3, ("Hello", 4), "over here"]

declare_syntax_cat name_dist
syntax nameWt := "(" ident "," num ")"
syntax nameWtList := "!{" nameWt,* "}"
syntax nameWtList : name_dist

def parseNameMap : Syntax → TermElabM (Array (Name × Nat))
  | `(name_dist|!{$[$xs:nameWt],*}) =>
    do
          let m : Array (Name × Nat) ←  xs.mapM (fun s => do
              match s with 
              | `(nameWt|($x:ident, $n:numLit)) =>                  
                  return (x.getId, (Syntax.isNatLit? n).get!)
              | _ =>
                throwError m!"{s} is not a valid nameWt"
              )
          m
  | _ => throwIllFormedSyntax

syntax (name:= constpack) "const!" name_dist : term
@[termElab constpack] def constpackImpl : TermElab := fun stx _ =>
    match stx with 
    | `(const! $s:name_dist) => 
        do
          let m : Array (Name × Nat) ←  parseNameMap s
          let c := m.map (fun (n, w) => (mkConst n, w))
          packWeighted c.toList
    | _ => throwIllFormedSyntax

#check const! !{(Nat.add, 2), (Nat.zero, 4)}


declare_syntax_cat evolver 
syntax "app" : evolver
syntax "name-app": evolver
syntax "binop": evolver
syntax "name-binop": evolver
syntax "rewrite": evolver
syntax "rewrite-flip": evolver
syntax "congr": evolver
syntax "eq-isles": evolver
syntax "all-isles": evolver
syntax "func-dom-isles": evolver
syntax "eq-closure": evolver
syntax "eq-closure" (expr_list)?: evolver
syntax "pi-goals": evolver

declare_syntax_cat evolve_transformer
syntax "by-type" (num)?: evolve_transformer

declare_syntax_cat evolver_list
syntax "^[" evolver,* (">>" evolve_transformer)? "]" : evolver_list

def parseEvolver : Syntax → TermElabM (RecEvolverM FullData)
| `(evolver|app) => (applyEvolver FullData).tautRec
| `(evolver|name-app) => (nameApplyEvolver FullData).tautRec
| `(evolver|binop) => (applyPairEvolver FullData).tautRec
| `(evolver|name-binop) => (nameApplyPairEvolver FullData).tautRec
| `(evolver|rewrite) => (rewriteEvolver true FullData).tautRec
| `(evolver|rewrite-flip) => (rewriteEvolver false FullData).tautRec
| `(evolver|congr) => (congrEvolver FullData).tautRec
| `(evolver|eq-isles) => eqIsleEvolver FullData
| `(evolver|all-isles) => allIsleEvolver FullData
| `(evolver|func-dom-isles) => funcDomIsleEvolver FullData
| `(evolver|eq-closure) => (eqSymmTransEvolver FullData).tautRec
| `(evolver|eq-closure $goals) => do
        let goals ← parseExprList goals
        (eqSymmTransEvolver FullData goals).tautRec
| `(evolver|pi-goals) => piGoalsEvolverM FullData

| stx => throwError m!"Evolver not implemented for {stx}"

def parseEvolverTrans : Syntax → TermElabM (ExprDist → TermElabM ExprDist)
| `(evolve_transformer|by-type) => return weightByType 1
| `(evolve_transformer|by-type $n) => do
      let n ← parseNat n
      return weightByType n
| stx => throwError m!"Evolver transformer not implemented for {stx}"


def parseEvolverList : Syntax → TermElabM (RecEvolverM FullData)  
  | `(evolver_list|^[$[$xs],*]) =>
    do
          let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
          return m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)
  | `(evolver_list|^[$[$xs],* >> $tr]) =>
    do
          let m : Array (RecEvolverM FullData) ←  xs.mapM <| fun s => parseEvolver s
          return (m.foldl (fun acc x => acc ++ x) (RecEvolverM.init FullData)).transformM 
                    <| ← parseEvolverTrans tr
  | _ => throwIllFormedSyntax

syntax (name:= evolution) 
  "evolve!" evolver_list (expr_list)? expr_dist (name_dist)? num num  : term
@[termElab evolution] def evolutionImpl : TermElab := fun s _ =>
match s with
| `(evolve! $evolvers $(goals?)? $initDist $(nameDist?)? $wb $card) => do
  let ev ← parseEvolverList evolvers
  let initDist ← parseExprMap initDist
  let nameDist? ← nameDist?.mapM  $ fun nameDist => parseNameMap nameDist
  let nameDist := nameDist?.getD #[]
  let nameDist := FinDist.fromList (nameDist.toList)
  let initData : FullData := (nameDist, [], [])
  let goals? ← goals?.mapM $ fun goals => parseExprList goals
  let goals := goals?.getD #[]
  let ev := ev.fixedPoint.evolve.andThenM (logResults goals)
  let wb ← parseNat wb
  let card ← parseNat card
  let finalDist ← ev wb card initData (← ExprDist.fromArray initDist) 
  let reportDist ← goals.filterMapM $ fun g => finalDist.getProof? g
  return ← (ppackWeighted reportDist.toList)
| _ => throwIllFormedSyntax

def syn: MacroM Syntax :=  `(evolver|app)
-- #check syn.run

def syn2: TermElabM Syntax :=  `(evolver_list|^[app, name-app])
-- #check syn2.run
def lstfromsyn:  TermElabM (RecEvolverM FullData)  :=  do
        let syn ← syn2
        parseEvolverList syn

-- #check lstfromsyn
