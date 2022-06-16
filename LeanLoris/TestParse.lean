import Lean
import Lean.Meta
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