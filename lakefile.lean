import Lake
open Lake DSL

package «lean-loris»{
  precompileModules := true
}

@[default_target]
lean_lib LeanLoris

@[default_target]
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

-- require aesop from git "https://github.com/JLimperg/aesop"

-- require mathlib3port from git
--   "https://github.com/leanprover-community/mathlib3port.git"@"master"