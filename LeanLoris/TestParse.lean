import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Std
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
syntax term "⊂" term : term
syntax term "∩" term : term


#eval checkTerm "a • s"

declare_syntax_cat term3

syntax term : term3
syntax "(" term3 ")" : term
syntax "λ" ident "," term3 : term3
syntax "λ"  ident ":" term3  "," term3 : term3
syntax "λ" "(" ident ":" term3 ")" "," term3 : term3
syntax "⇑" term3 : term
macro_rules
| `(term3|$x:term) => `($x)
| `(term3|λ $x:ident : $type:term , $y:term) => 
  `(fun ($x : $type)  => $y)
| `(term3|λ ( $x:ident : $type:term ) , $y:term) => 
  `(fun ($x : $type)  => $y)

def checkTerm3 (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := runParserCategory env `term3  s
  match chk with
  | Except.ok _  => pure true
  | Except.error _  => pure false

#eval checkTerm "λ x : Nat, x + 1"
#eval checkTerm3 "λ x : Nat, x + 1"
#eval checkTerm3 "B (λ (t : finset α), s ∩ t)"

def checkStatements : MetaM (List (String × Bool × Bool)) := do
  let prompts ← depsPrompt
  (prompts.toList.take 50).mapM fun s => 
    do return (s, ← checkTerm s, ← checkTerm3 s)

#eval checkStatements


syntax(name:= lean3syn) "lean3" term3 : term
@[termElab lean3syn] def elab3: Term.TermElab := fun s typ? =>  
  do
  match s with
  | `(lean3 $x:term3) => do 
      Term.elabTerm x typ?
  | _ => throwIllFormedSyntax 

def eg3 := lean3 λ x : Nat, x + 1
#print eg3
def eg3' := lean3 λ (x : Nat), x + 1
#print eg3