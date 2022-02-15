import LeanLoris.Syntax 


def idPropTest(A: Prop) :=
  let idA := ∀ a : A, A
  let seek := evolve! ^[pi-goals] %[idA] %{(idA, 0)} 1 1000
  ()

def appTest(A B: Prop)(a : A)(f: A → B) :=
  let seek := evolve! ^[app] %[B] %{(f, 0), (a, 0)} 1 1000
  ()

def mpTest(A B: Prop) :=
  let mp := A → (A → B)→ B
  let seek := evolve! ^[pi-goals, app] %[mp] %{(mp, 0)} 1 1000
  ()

def rflTest(A: Type) :=
  let p := ∀ a: A, a = a
  let seek := evolve! ^[pi-goals, rfl] %[p] %{(p, 0)} 1 1000
  ()