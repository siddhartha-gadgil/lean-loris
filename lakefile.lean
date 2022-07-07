import Lake
open Lake DSL

package «lean-loris» 

lean_lib LeanLoris

@[defaultTarget]
lean_exe all {
  supportInterpreter := true
}

lean_exe czsl_oly {
  supportInterpreter := true
}

lean_exe local_const {
  supportInterpreter := true
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"master"