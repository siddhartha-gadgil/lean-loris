import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledLclCnst
import LeanLoris.ExprDist
import LeanLoris.ConstDeps
import Mathlib
open CzSl ExprDist Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def mathDepData(mathenv: Environment) : IO Unit := do
  IO.println "counting dependencies"
  let offCore := offSpringTripleCore
  let ei := offCore.run' {maxHeartbeats := 100000000000} {env := mathenv}
  match ←  ei.toIO' with
  | Except.ok triples => 
      IO.println "\nData obtained"
      IO.println triples.size 
      let data ← FrequencyData.get triples
      let terms ← data.termFreqData
      let types ← data.typeFreqData
      let pairs := data.typeTermFreqs
      IO.println s!"pairs:{pairs.size}"
      let file := System.mkFilePath ["data/type-terms.json"]
      let typeTerm := data.typeTermView
      IO.FS.writeFile file typeTerm
      let file := System.mkFilePath ["data/matrices.json"]
      let matrices := matrixView triples
      IO.FS.writeFile file matrices
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  return ()

def runRecEg(env: Environment) : IO Unit := do
  IO.println "\nRecursion example"
  let c := coreView RecEg.view3
  let ei := c.run' {maxHeartbeats := 100000000000} {env := env}
  let view := ei.toIO <| fun e => IO.Error.userError $ "Error while running" 
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\n# Run completed\n"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg

def runCzSl(env: Environment) : IO Unit := do
  IO.println "\nCzech-Slovak Olympiad example\n"
  let c := coreView view4
  let ei := c.run' {maxHeartbeats := 100000000000} {env := env}
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\n# Run completed\n"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg

def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot?) ["build/lib", "lean_packages/mathlib/build/lib/"]
  let env ← 
    importModules [{module := `LeanLoris.CompiledCzSl}, {module := `LeanLoris.CompiledLclCnst}] {}
  let mathenv ← 
    importModules [{module := `Mathlib}] {}
  IO.println "Choose one or more of the following:"
  IO.println "1. Recursion example"
  IO.println "2. Czech-Slovak Olympiad example"
  IO.println "3. Dependency generation"
  if args.contains "1" then runRecEg env
  if args.contains "2" then runCzSl env
  if args.contains "3" then mathDepData mathenv
  return ()
