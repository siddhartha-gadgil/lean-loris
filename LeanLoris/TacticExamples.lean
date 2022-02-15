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

set_option maxHeartbeats 100000000

def recTest(f: Nat → Nat) :=
  let p := (∀ x: Nat, f (x + 1) = f x) → ∀ x: Nat, f x = 0
  let seek := evolve! ^[pi-goals, rfl, eq-closure, nat-rec] %[p] %{(p, 0)} 2 5000
  ()