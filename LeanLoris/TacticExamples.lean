import LeanLoris.Syntax 


def idPropTest(A: Prop) :=
  let idA := ∀ a : A, A
  let seek := evolve! ^[pi-goals] %[idA] %{(idA, 0)} 2 1000
  ()

def mpTest(A B: Prop) :=
  let mp := A → (A → B)→ B
  let seek := evolve! ^[pi-goals, app] %[mp] %{(mp, 0)} 4 1000
  ()