import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledRecEg
import LeanLoris.ExprDist
import LeanLoris.ConstDeps
import Mathlib
open CzSl ExprDist Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false
def main : IO Unit := do
  initSearchPath (← Lean.findSysroot?) ["build/lib", "lean_packages/mathlib/build/lib/"]
  let env ← 
    importModules [{module := `LeanLoris.CompiledCzSl}, {module := `LeanLoris.CompiledRecEg}] {}
  let mathenv ← 
    importModules [{module := `Mathlib}] {}
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
      -- IO.println s!"terms:\n${terms}"
      -- IO.println s!"types:\n${types}"
      let pairs := data.typeTermFreqs
      IO.println s!"pairs:{pairs.size}"
      -- let pickData := data.termPickData
      -- let pickData := pickData.toList.take 3000
      -- IO.println s!"significant pairs: {pickData}"
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
  IO.println "\nRecursion example"
  let c := coreView RecEg.view3
  let ei := c.run' {maxHeartbeats := 100000000000} {env := env}
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
  let ei := c.run' {maxHeartbeats := 100000000000} {env := env}
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\nRun completed"
      IO.println view 
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  return ()
