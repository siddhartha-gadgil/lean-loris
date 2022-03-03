import LeanLoris.Syntax 


def idPropTest(A: Prop) :=
  let idA := ∀ a : A, A
  let seek := evolve! ev![pi-goals-all] exp![idA] exp!{(idA, 0)} 1 1000
  ()

def appTest(A B: Prop)(a : A)(f: A → B) :=
  let seek := evolve! ev![app] exp![B] exp!{(f, 0), (a, 0)} 1 1000
  ()

def mpTest(A B: Prop) :=
  let mp := A → (A → B)→ B
  let seek := evolve! ev![pi-goals, simple-app] exp![mp] exp!{(mp, 0)} 1 1000
  ()

def rflTest(A: Type) :=
  let p := ∀ a: A, a = a
  let seek := evolve! ev![pi-goals, rfl] exp![p] exp!{(p, 0)} 1 1000
  ()

set_option maxHeartbeats 100000000

def recTest(f: Nat → Nat) :=
  let p := (∀ x: Nat, f (x + 1) = f x) → (∀ x: Nat, f x = f 0)
  let hyp := ∀ x: Nat, f (x + 1) = f x
  let seek := evolve! ev![pi-goals, rfl, eq-closure, nat-rec, app, binop] 
            exp![p, 
            hyp → f 0 = f 0, 
            hyp → (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0),
            hyp → (∀ (n : Nat), f n = f 0 → f (n + 1) = f n),
            hyp → f 0 = f 0 → (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0) → ∀ (n : Nat), f n = f 0] exp!{(p, 0)} 2 5000
  let step := hyp → (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0)
  let stepPf : step := fun h n ih => Eq.trans (h n) ih
  let seek2 := evolve! ev![pi-goals, rfl, eq-closure, nat-rec, app, binop] 
            exp![p, 
            hyp → f 0 = f 0, 
            hyp → (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0),
            hyp → (∀ (n : Nat), f n = f 0 → f (n + 1) = f n),
            hyp → f 0 = f 0 → (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0) → ∀ (n : Nat), f n = f 0] exp!{(p, 0), (stepPf, 1)} 2 5000
  let base : Prop := hyp → f 0 = f 0
  let basePf : base := fun hyp => Eq.refl (f 0)
  let recFn := fun _ : hyp => natRec (fun n => f n = f 0)
  let seek3 := evolve! ev![simple-binop] exp![p, 
            hyp → f 0 = f 0, 
            hyp → (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0),
            hyp → (∀ (n : Nat), f n = f 0 → f (n + 1) = f n),
            hyp → f 0 = f 0 → (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0) → ∀ (n : Nat), f n = f 0] exp!{(p, 0), (basePf, 0), (recFn, 0), (stepPf, 0)} 2 5000
  let pf : p := fun h => (recFn h) (basePf h) (stepPf h)
  ()


#check @Nat.brecOn
