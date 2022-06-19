import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledLclCnst
import LeanLoris.ExprDist
import LeanLoris.ConstDeps
open CzSl ExprDist Lean

def lclConstDocs: String :=
"Our main example of mixed reasoning is the result that if f: Nat → α is a function from natural numbers to a type α such that ∀ n : Nat, f (n + 1) = f n, then ∀n : Nat, f n = f 0, i.e. f is a constant function if it is locally constant.\n"

def runLclConst(env: Environment) : IO Unit := do
  IO.println s!"\n# Induction: locally constant functions\n\n{lclConstDocs}"
  let c := coreView LclConst.view3
  let ei := c.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000} {env := env}
  let view := ei.toIO <| fun e => IO.Error.userError $ "Error while running" 
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\n# Run completed\n"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg

def main  : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lean_packages/mathlib/build/lib/"]
  let env ← 
    importModules [{module := `LeanLoris.CompiledCzSl}, {module := `LeanLoris.CompiledLclCnst}] {}
  runLclConst env
  return ()