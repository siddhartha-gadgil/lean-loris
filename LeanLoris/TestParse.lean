import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Init.System
import Std
import LeanLoris.Utils
import LeanLoris.ExprPieces
import LeanLoris.ConstDeps
import Lean.Data.Json.Basic
import Lean.Data.Json.Printer
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import Mathlib.Algebra.Group.Defs
open Lean Meta Std Elab Parser 

def depsPrompt : IO (Array String) := do
  let file := System.mkFilePath ["data/types.txt"]
  IO.FS.lines file

def numPrompts : IO Nat := do
  let prompts ← depsPrompt
  pure $ prompts.size

-- #eval numPrompts

def checkTerm (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := runParserCategory env `term  s
  match chk with
  | Except.ok _  => pure true
  | Except.error _  => pure false

#eval checkTerm "(fun x : Nat => x + 1)"

syntax term "•" term : term
syntax term "⊆" term : term

#eval checkTerm "a • s"

def checkStatements : MetaM (List (String × Bool)) := do
  let prompts ← depsPrompt
  (prompts.toList.take 20).mapM fun s => do return (s, ← checkTerm s)

#eval checkStatements

declare_syntax_cat term3

syntax term : term3
syntax "λ" ident "," term3 : term3
syntax "λ"  ident ":" term3  "," term3 : term3
macro_rules
| `(term3|$x:term) => `($x)
| `(term3|λ $x:ident : $type:term , $y:term) => 
  `(fun ($x : $type)  => $y)

def checkTerm3 (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := runParserCategory env `term3  s
  match chk with
  | Except.ok _  => pure true
  | Except.error _  => pure false

#eval checkTerm "λ x : Nat, x + 1"
#eval checkTerm3 "λ x : Nat, x + 1"


syntax(name:= lean3syn) "lean3" term3 : term
@[termElab lean3syn] def elab3: Term.TermElab := fun s typ? =>  
  do
  match s with
  | `(lean3 $x:term) => do 
      Term.elabTerm x typ?
  | `(lean3 λ $x:ident : $type:term3 , $y:term3) => 
      let stx ←  `(fun ($x : $type)  => $y)
      Term.elabTerm stx typ?
  | _ => throwIllFormedSyntax 

def eg3 := lean3 λ x : Nat, x + 1
#print eg3