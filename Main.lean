import LeanLoris
import Lean.Meta
import LeanLoris.ElabCzSl
import LeanLoris.ExprDist
open CzSl ExprDist Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false
def main : IO Unit := do
  let c := coreView view4
  initSearchPath (← Lean.findSysroot?) ["build/lib"]
  let env ← importModules [{module := `LeanLoris.ElabCzSl}] {}
  let ei := c.run' {maxHeartbeats := 100000000000} {env}
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\nRun completed"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  return ()
