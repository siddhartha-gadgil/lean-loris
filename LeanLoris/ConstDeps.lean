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

def inferTypeOpt(e: Expr) : MetaM (Option Expr) := do
  try
    let type ← inferType e
    return some type
  catch _ => return none

partial def recExprNames: Expr → MetaM (List Name) :=
  fun e =>
  do 
  -- match ← getCached? e with
  -- | some offs => return offs
  -- | none =>
    -- IO.println s!"recExprNames: ${e}"
    let res ← match e with
      | Expr.const name _ _  =>
        do
        if ← (isWhiteListed name) 
          then return [name] 
          else
          if ← (isNotAux name)  then
            match ←  nameExpr?  name with
            | some e => recExprNames e
            | none => return []
          else pure []        
      | Expr.app f a _ => 
          do  
            -- let ftype ← inferTypeIO f env
            let ftypeOpt ← inferTypeOpt f 
            let explOpt := 
              ftypeOpt.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := explOpt.getD true
            let fdeps ← recExprNames f
            let adeps ← recExprNames a
            let s := 
              if !expl then fdeps else
                fdeps ++ adeps
            return s.eraseDups
      | Expr.lam _ _ b _ => 
          do
            return ← recExprNames b 
      | Expr.forallE _ _ b _ => do
          return  ← recExprNames b 
      | Expr.letE _ _ _ b _ => 
            return ← recExprNames b
      | _ => pure []
    -- cache e res
    -- IO.println s!"found result recExprNames: ${e}"
    return res


def offSpring? (name: Name) : MetaM (Option (Array Name)) := do
  -- IO.println "finding offspring"
  let expr ← nameExpr?  name
  -- IO.println "found expr opt"
  match expr with
  | some e => 
    -- IO.println s!"found expr {e}"
    return  some <| (← recExprNames e).toArray
  | none => return none

partial def descendants (name: Name) : MetaM (Array Name) := do
  let offOpt ← offSpring? name
  match offOpt with 
  | some off => do
      let recDesc ← off.mapM (fun n => descendants n)
      return recDesc.foldl (fun acc n => acc.append n) #[name]
  | none => return #[name]

def exprDescendants (expr: Expr) : MetaM (Array Name) := do
  -- IO.println s!"exprDescendants: {expr}"
  let offs ← recExprNames expr
  let groups ← offs.toArray.mapM (fun n => descendants n)
  return groups.foldl (fun acc n => acc.append n) #[]

def offSpringTriple(excludePrefixes: List Name := [])
              : MetaM (Array (Name × (Array Name) × (Array Name) )) :=
  do
  let keys ←  constantNameTypes  
  IO.println s!"keys: {keys.size}"
  let goodKeys := keys.filter fun (name, _) =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name))
  IO.println s!"good-keys: {goodKeys.size}"
  let kv : Array (Name × (Array Name) × (Array Name)) ←  (goodKeys).mapM $ 
      fun (n, type) => 
          do 
          -- IO.println $ "descendants of " ++ n ++ ": " 
          let l := (← offSpring? n).getD #[]
          let l := l.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          -- IO.println $ "found descendants of " ++ n ++ ": "
          let tl ←  recExprNames type
          -- IO.println $ "found type descendants of " ++ n ++ ": "
          let tl := tl.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          return (n, l, tl.toArray)
  return kv

def offSpringTripleCore: 
    CoreM (Array (Name × (Array Name) × (Array Name) )) := 
          (offSpringTriple [`Lean, `Std, `IO, 
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO]).run' 

#check @Lean.instToExprOption
#check Lean.LocalContext.foldrM
#check Expr.isType