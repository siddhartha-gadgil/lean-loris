import LeanLoris
import Lean.Meta
import LeanLoris.ElabCzSl
open ElabCzSl Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false
def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  let c3 := coreList rep3
  initSearchPath (← Lean.findSysroot?) ["build/lib"]
  let env ← importModules [{module := `LeanLoris.ElabCzSl}] {}
  let ei3 := c3.run' {maxHeartbeats := 100000000000} {env}
  match ←  ei3.toIO' with
  | Except.ok arr => IO.println "ran fine" 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
