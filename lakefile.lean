import Lake
open Lake DSL

package «lean-loris» {
  supportInterpreter := true
}



require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"
