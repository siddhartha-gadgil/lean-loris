import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledLclCnst
import LeanLoris.ExprDist
import LeanLoris.ConstDeps
open CzSl ExprDist Lean

def runCzSl(env: Environment) : IO Unit := do
  IO.println s!"\n# Czech-Slovak Olympiad example\n\n{czslDocs}"
  let c := coreView view4
  let ei := c.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000} {env := env}
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
  runCzSl env
  return ()
