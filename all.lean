import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledLclCnst
import LeanLoris.ExprDist
import LeanLoris.ConstDeps
import Mathlib
open CzSl ExprDist Lean

/-
Running computationally expensive code. Specifically, depending on the command line arguments, three things can be run.
1. A Czech-Slovak Olympiad problem: purely forward reasoning.
2. Mixed reasoning: functions satisfying `∀ n: Nat, f(n + 1) = f(n)` are constants.
3. Generation of dependency data for machine learning.
4. Generation of shallow dependency data for machine learning.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def mathDepFullData(mathenv: Environment) : IO Unit := do
  IO.println "\n# Dependencies for data for machine learning.\n"
  IO.println "We consider dependencies in MathLib4 and generate various forms of data for machine learning. As of now these are for basic experiments.\n"
  let offCore := offSpringTripleCore
  let ei := offCore.run' 
      {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := mathenv}
  match ←  ei.toIO' with
  | Except.ok triples => 
      IO.println "\nData obtained"
      IO.println s!"Using {triples.size} definitions" 
      let data ← FrequencyData.get triples
      let terms ← data.termFreqData
      let types ← data.typeFreqData
      let pairs := data.typeTermFreqs
      IO.println s!"Obtained {pairs.size} term-type pairs"
      let file := System.mkFilePath ["data/type-terms.json"]
      let typeTerm := data.typeTermView
      IO.FS.writeFile file typeTerm
      let file := System.mkFilePath ["data/frequencies.json"]
      let freqJsonC : CoreM Json := data.asJson
      let (freqJson, _) ←   freqJsonC.toIO 
          {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := mathenv}
      let freqs := freqJson.pretty
      IO.FS.writeFile file freqs
      let file := System.mkFilePath ["data/matrices.json"]
      let matrices := matrixView triples
      IO.FS.writeFile file matrices
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  return ()

def mathDepData(mathenv: Environment) : IO Unit := do
  IO.println "\n# Dependencies for data for machine learning.\n"
  IO.println "We consider dependencies in MathLib4 and generate various forms of data for machine learning. As of now these are for basic experiments.\n"
  let offCore := offSpringShallowTripleCore
  let ei := offCore.run' 
      {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := mathenv}
  match ←  ei.toIO' with
  | Except.ok triples => 
      IO.println "\nData obtained"
      IO.println s!"Using {triples.size} definitions" 
      let data ← FrequencyData.withMultiplicity triples
      let file := System.mkFilePath ["data/shallow-frequencies.json"]
      let freqJsonC : CoreM Json := data.asJson
      let (freqJson, _) ←   freqJsonC.toIO 
          {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := mathenv}
      let freqs := freqJson.pretty
      IO.FS.writeFile file freqs
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  return ()

def mathPrompt(mathenv: Environment) : IO Unit := do
  IO.println "\n# Propmpts for premises for machine learning.\n"
  IO.println "We consider dependencies in MathLib4 and generate data for simple prompts. As of now these are for basic experiments.\n"
  let promptCore := prompCoreJs
  let ei := promptCore.run'   
      {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := mathenv}
  match ←  ei.toIO' with
  | Except.ok view => 
      IO.println "\nData obtained"
      let file := System.mkFilePath ["data/simple-prompts.json"]
      IO.FS.writeFile file view
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
  return ()

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

def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lean_packages/mathlib/build/lib/"]
  let env ← 
    importModules [{module := `LeanLoris.CompiledCzSl}, {module := `LeanLoris.CompiledLclCnst}] {}
  let mathenv ← 
    importModules [{module := `Mathlib}] {}
  IO.println "Choose one or more of the following:"
  IO.println "1. Czech-Slovak Olympiad example"
  IO.println "2. Induction: locally constant functions"
  IO.println "3. Dependency generation"
  IO.println "4. Shallow dependency generation"
  IO.println "5. Dependency prompt generation"
  if args.contains "2" then runLclConst env
  if args.contains "1" then runCzSl env
  if args.contains "3" then mathDepFullData mathenv
  if args.contains "4" then mathDepData mathenv
  if args.contains "5" then mathPrompt mathenv
  return ()
