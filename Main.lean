import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledRecEg
import LeanLoris.ExprDist
import LeanLoris.ConstDeps
open CzSl ExprDist Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false
def main : IO Unit := do
  initSearchPath (← Lean.findSysroot?) ["build/lib"]
  let env ← 
    importModules [{module := `LeanLoris.CompiledCzSl}, {module := `LeanLoris.CompiledRecEg},
        {module := `LeanLoris.ConstDeps}] {}
  IO.println "counting dependencies"
  let offCore := offSpringTripleCore
  let ei := offCore.run' {maxHeartbeats := 100000000000} {env}
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\nRun completed"
      IO.println view.size 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  IO.println "Recursion example"
  let c := coreView RecEg.view3
  let ei := c.run' {maxHeartbeats := 100000000000} {env}
  let view := ei.toIO <| fun e => IO.Error.userError $ "Error while running" 
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\nRun completed"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  -- IO.println "\nBinop"
  -- let c := coreView RecEg.view0
  -- let ei := c.run' {maxHeartbeats := 100000000000} {env}
  -- match ←  ei.toIO' with
  -- | Except.ok view => 
  --     IO.println view 
  -- | Except.error e =>
  --   do
  --         let msg ← e.toMessageData.toString
  --         IO.println msg
  IO.println "\nCzech-Slovak Olympiad example"
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
