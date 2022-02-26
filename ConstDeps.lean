import Lean
import Lean.Meta
import Init.System
import Std.Data.HashMap
import LeanLoris.Utils
import LeanLoris.ExprPieces
open Lean Meta

def constantNames  : MetaM (Array Name) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, _) => name 
  let names ← allNames.filterM (isWhiteListed)
  return names

def constantNameTypes  : MetaM (Array (Name ×  Expr)) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, dfn) => (name, dfn.type) 
  let names ← allNames.filterM (fun (name, _) => isWhiteListed name)
  return names


def offSpring? (name: Name) : MetaM (Option (Array Name)) := do
  let expr ← nameExpr?  name
  match expr with
  | some e => return  some <| (← exprNames false e).toArray
  | none => return none

partial def descendants (name: Name) : MetaM (Array Name) := do
  let offOpt ← offSpring? name
  match offOpt with 
  | some off => do
      let recDesc ← off.mapM (fun n => descendants n)
      return recDesc.foldl (fun acc n => acc.append n) #[name]
  | none => return #[name]

def exprDescendants (expr: Expr) : MetaM (Array Name) := do
  let offs ← exprNames false expr
  let groups ← offs.toArray.mapM (fun n => descendants n)
  return groups.foldl (fun acc n => acc.append n) #[]

def offSpringTriple(excludePrefixes: List Name := [])
              : MetaM (Array (Name × (Array Name) × (Array Name) )) :=
  do
  let keys ←  constantNameTypes  
  let goodKeys := keys.filter fun (name, _) =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name))
  let kv : Array (Name × (Array Name) × (Array Name)) ←  (goodKeys).mapM $ 
      fun (n, type) => 
          do 
          let l ← descendants n
          let l := l.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          let tl ←  exprDescendants type
          let tl := tl.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          return (n, l, tl)
  return kv

def offSpringTripleCore: 
    CoreM (Array (Name × (Array Name) × (Array Name) )) := 
          (offSpringTriple ).run' 
