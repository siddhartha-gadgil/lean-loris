import LeanLoris
import Lean.Meta
import LeanLoris.CompiledCzSl
import LeanLoris.CompiledLclCnst
import LeanLoris.ExprDist
import LeanLoris.ConstDeps
open CzSl ExprDist Lean

def czslDocs : String := 
"Our main model problem for forward reasoning is the following from a Czech-Slovak Olympiad:

Let M be a set with a product. Given the axioms:
* ∀ a b : M, (a * b) * b = a
* ∀ a b : M, a * (a * b) = b
then, for arbitrary elements m and n in M, we have m * n = n * m.

We fix m and n and reason forward starting with m, n, the axioms, and multiplication. Our forward reasoning is tuned for this problem, and also mildly help by including m *n in the initial state. But we do not use the statement of the problem, any of the lemmas or the proof.

To understand the (automated) reasoning steps (and for use during tuning and debugging), some lemmas and the theorem were defined. While running progress in proving these is logged.

* def lem1! := (m * n) * n = m 
* def lem2! := (m * n) * ((m * n) * n) = n
* def lem3! := ((m * n) * m) * m = m * n
* def lem4! := (m * n) * ((m * n) * n) = (m * n) * m
* def lem5! := (m * n) * m = n
* def lem6! := ((m * n) * m) * m = n * m
* def thm! := m * n = n * m

The progress in proving the lemmas is output at each intermediate step, and finally the proof obtained for the theorem. Running takes a couple of minutes (more on a slower machine).\n"

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
