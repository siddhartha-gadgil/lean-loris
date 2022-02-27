import Lake
open Lake DSL

package «lean-loris» {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "042ca5df88a027d579648750fda03266f566a876"
  }],
  supportInterpreter := true
}
