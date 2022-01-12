import LeanLoris.Core
import Lean.Meta
import Lean.Elab
import Std
open Std
open Lean Meta Elab Term

initialize expNamesCache : IO.Ref (HashMap Expr (List Name)) ← IO.mkRef (HashMap.empty)

def getCachedNames? (e : Expr) : IO (Option (List Name)) := do
  let cache ← expNamesCache.get
  return (cache.find? e)

def cacheName (e: Expr) (offs : List Name) : IO Unit := do
  let cache ← expNamesCache.get
  expNamesCache.set (cache.insert e offs)
  return ()

def nameExpr? : Name → TermElabM ( Option Expr) := 
  fun name => do
      let info := ((← getEnv).find? name)
      return Option.bind info ConstantInfo.value?

-- does not look within types for lambda's and pi's
partial def exprNames: Expr → TermElabM (List Name) :=
  fun e =>
  do 
  match ← getCachedNames? e with
  | some offs => return offs
  | none =>
    let res ← match e with
      | Expr.const name _ _  =>
        do
        if ← (isWhiteListed name) 
          then [name] 
          else
          if ← (isNotAux  name)  then
            match ← nameExpr?  name with
            | some e => exprNames e
            | none => []
          else []        
      | Expr.app f a _ => 
          do  
            let ftype ← inferType f 
            let expl := ftype.data.binderInfo.isExplicit
            let fdeps ← exprNames f
            let adeps ← exprNames a
            let s := 
              if !expl then fdeps else
                fdeps ++ adeps
            return s.eraseDups
      | Expr.lam _ _ b _ => 
          do
            return ← exprNames b 
      | Expr.forallE _ _ b _ => do
          return  ← exprNames b 
      | Expr.letE _ _ _ b _ => 
            return ← exprNames b
      | _ => []
    cacheName e res
    return res
