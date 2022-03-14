import Lake
open Lake DSL

package «lean-loris» {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "0bdee9fa7f180c43a9ca75fd714e49125d0a2861"
  }],
  supportInterpreter := true
}
