import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledRecEg
import LeanLoris.ExprDist
open CzSl ExprDist Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false
def main : IO Unit := do
  IO.println "Recursion example"
  initSearchPath (← Lean.findSysroot?) ["build/lib"]
  let env ← importModules [{module := `LeanLoris.CompiledCzSl}, {module := `LeanLoris.CompiledRecEg}] {}
  let c := coreView RecEg.view1
  let ei := c.run' {maxHeartbeats := 100000000000} {env}
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\nRun completed"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  -- IO.println "Second round"
  -- let c := coreView RecEg.view2
  -- let ei := c.run' {maxHeartbeats := 100000000000} {env}
  -- match ←  ei.toIO' with
  -- | Except.ok view => 
  --     IO.println "\nRun completed"
  --     IO.println view 
  -- | Except.error e =>
  --   do
  --         let msg ← e.toMessageData.toString
  --         IO.println msg
  IO.println "\nBinop"
  let c := coreView RecEg.view0
  let ei := c.run' {maxHeartbeats := 100000000000} {env}
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\nRun completed"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  IO.println "Czech-Slovak Olympiad example"
  let c := coreView view4
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
