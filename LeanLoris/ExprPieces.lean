import LeanLoris.Utils
import Lean.Meta
import Lean.Elab
import Std
open Std
open Lean Meta Elab Term

initialize expNamesCache : IO.Ref (HashMap Bool (HashMap Expr (List Name))) ← IO.mkRef (HashMap.empty)

def getCachedNames? (withDoms: Bool)(e : Expr) : IO (Option (List Name)) := do
  let cache ← expNamesCache.get
  return (cache.find? withDoms).bind (fun m => m.find? e)

def cacheName (withDoms: Bool)(e: Expr) (offs : List Name) : IO Unit := do
  let cache ← expNamesCache.get
  let prev := cache.findD withDoms HashMap.empty
  expNamesCache.set (cache.insert withDoms $ prev.insert e offs)
  return ()

def nameExpr? : Name → MetaM ( Option Expr) := 
  fun name => do
      let info := ((← getEnv).find? name)
      return Option.bind info ConstantInfo.value?

partial def exprHash : Expr → TermElabM UInt64 
  | e =>
    match e with
      | Expr.const name _ _  =>
        do
        let type? ← inferType? e
        let isForAll := (type?.map (fun type => type.isForall)).getD true
        if isForAll then return 7
        else
          match ← nameExpr?  name with
          | some e => exprHash e
          | none => return 7
      | Expr.app f a _ => 
          do  
            let ftype? ← inferType? f 
            let expl? := 
              ftype?.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := expl?.getD true
            if !expl then pure 7 else return mixHash (← exprHash f) (← exprHash a)
      | Expr.lam _ t b _ => 
          return mixHash (← exprHash t) (← exprHash b)
      | Expr.forallE _ t b _ => do
          return mixHash (← exprHash t) (← exprHash b) 
      | Expr.letE _ t v b _ => 
          return mixHash (← exprHash t) (← exprHash b)
      | Expr.lit _ d => return d.hash
      | _ => return 7


/-- 
Finding whether an expression is contained in another; to be used in (not yet implemented) transformations that reduce weights for sub-expressions of goals.
-/
partial def subExpr?(withDoms: Bool)(parent: Expr): Expr → TermElabM Bool := 
    fun e => do
      if ← isDefEq parent e then return true
      else
      match ← whnf e with
        | Expr.app f a _ => 
            (subExpr? withDoms parent f) <||>
                  (subExpr? withDoms parent a)
        | Expr.lam _ t b _ => 
            (subExpr? withDoms parent b) <||>
                  (pure withDoms) <&&>  (subExpr? withDoms parent t)
        | Expr.forallE _ t b _ => 
            (subExpr? withDoms parent b) <||>
                  (pure withDoms) <&&>  (subExpr? withDoms parent t)
        | Expr.letE _ t v b _ => do
            (subExpr? withDoms parent b) <||>
                  (subExpr? withDoms parent v) <||>
                  (pure withDoms) <&&>  (subExpr? withDoms parent t)
        | _ => return false

/--
Computing optional weight based on whether an expression is contained in another.
-/
def subExprWeight(cost: Nat)(withDoms: Bool)(parent: Expr): Expr → TermElabM (Option Nat) :=
    fun e => do
        if (← subExpr? withDoms parent e) then return (some cost) else return none

-- None of the code below is currently used; it remains from other approaches (and is kept for possible changes in approach)

-- does not look within types for lambda's and pi's
partial def exprNames (withDoms : Bool): Expr → MetaM (List Name) :=
  fun e =>
  do 
  match ← getCachedNames? withDoms e with
  | some offs => return offs
  | none =>
    let res ← match e with
      | Expr.const name _ _  =>
        do
        if ← (isWhiteListed name) 
          then return [name] 
          else
          if ← (isNotAux  name)  then
            match ← nameExpr?  name with
            | some e => exprNames withDoms e
            | none => return []
          else return []        
      | Expr.app f a _ => 
          do  
            let ftype? ← inferType? f 
            let expl? := 
              ftype?.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := expl?.getD true            let fdeps ← exprNames withDoms f
            let adeps ← exprNames withDoms a
            let s := 
              if !expl then fdeps else
                fdeps ++ adeps
            return s.eraseDups
      | Expr.lam _ t b _ => 
          do
            if withDoms then
              do
              let tdeps ← exprNames withDoms t
              let bdeps ← exprNames withDoms b
              return (tdeps ++ bdeps)
            else
              return ← exprNames withDoms b 
      | Expr.forallE _ t b _ => do
          if withDoms then
              do
              let tdeps ← exprNames withDoms t
              let bdeps ← exprNames withDoms b
              return (tdeps ++ bdeps)
            else
              return ← exprNames withDoms b 
      | Expr.letE _ t v b _ => 
            if withDoms then
              do
              let tdeps ← exprNames withDoms t
              let bdeps ← exprNames withDoms b
              let vdeps ← exprNames withDoms v
              return (tdeps ++ bdeps ++ vdeps)
            else
              do
              let bdeps ← exprNames withDoms b
              let vdeps ← exprNames withDoms v
              return (bdeps ++ vdeps)
      | _ => return []
    cacheName withDoms e res
    return res

partial def argList : Expr → TermElabM (List Name) :=
  fun e => do
    let res ← match e with
      | Expr.const name _ _  =>
        do
        let type? ← inferType? e
        let isForAll := (type?.map (fun type => type.isForall)).getD true
        if isForAll then return []
        else
        if ← (isWhiteListed name) 
          then return [name] 
          else
          if ← (isNotAux  name)  then
            match ← nameExpr?  name with
            | some e => argList e
            | none => return []
          else return []        
      | Expr.app f a _ => 
          do  
            let ftype? ← inferType? f 
            let expl? := 
              ftype?.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := expl?.getD true
            if !expl then pure [] else return (← argList f) ++ (← argList a)
      | Expr.lam _ t b _ => 
          argList b 
      | Expr.forallE _ t b _ => do
          argList b 
      | Expr.letE _ t v b _ => 
          argList b
      | _ => return []
    return res


-- Verbose hashing for debugging (not used currently)
partial def exprHashV : Expr → TermElabM UInt64 :=
  fun e => do 
    logInfo m!"computing hash of {e}"
    match e with
      | Expr.const name _ _  =>
        do
        logInfo m!"{e} is a constant {name}"
        let type? ← inferType? e
        let isForAll := (type?.map (fun type => type.isForall)).getD true
        if isForAll then
          logInfo m!"{e} is forall" 
          return 7
        else
          match ← nameExpr?  name with
          | some e => exprHashV e
          | none => 
            logInfo m!"{e} is a name {name} with no definition"
            return 7
      | Expr.app f a _ => 
          do  
            logInfo m!"{e} is {f} applied to {a}" 
            let ftype? ← inferType? f 
            let expl? := 
              ftype?.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := expl?.getD true
            if !expl then
              logInfo m!"{e} isa function with argument not explicit" 
              pure 7 
            else
              logInfo m!"Mixing hash of {f} and {a}" 
              return mixHash (← exprHashV f) (← exprHashV a)
      | Expr.lam _ t b _ => 
          logInfo m!"{e} is a lambda {t} {b}"
          return mixHash (← exprHashV t) (← exprHashV b)
      | Expr.forallE _ t b _ => do
          logInfo m!"{e} is a forall {t} {b}"
          return mixHash (← exprHashV t) (← exprHashV b) 
      | Expr.letE _ t v b _ => 
          logInfo m!"{e} is a let {t} {v} {b}"
          return mixHash (← exprHashV t) (← exprHashV b)
      | Expr.lit _ d => 
          logInfo m!"{e} is a literal"
          return d.hash
      | _ =>
          logInfo m!"{e} is a weird expression {← whnf e} with hash {e.hash}" 
          return 7


