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

def localConst0(f: Nat → Nat) :=
  let hyp! := ∀ x: Nat, f (x + 1) = f x
  let claim! := ∀ n: Nat, f n = f 0
  let baseclaim! := f 0 = f 0
  let base! : Prop := hyp! → baseclaim!
  let base : base! := fun hyp => Eq.refl (f 0)
  let stepclaim! := (∀ (n : Nat), f n = f 0 → f (n + 1) = f 0)
  let step! := hyp! → stepclaim!
  let step : step! := fun h n ih => Eq.trans (h n) ih
  let semistepclaim! := (∀ (n : Nat), f n = f 0 → f (n + 1) = f n)
  let semistep! := hyp! → semistepclaim!
  let semistep : semistep! := fun hyp n _ => hyp n
  let recFn! := hyp! → baseclaim! → stepclaim! → claim!
  let recFn : recFn! := fun _ : hyp! => natRec (fun n => f n = f 0)
  let thm! := (∀ x: Nat, f (x + 1) = f x) → (∀ x: Nat, f x = f 0)
  let seek := evolve! ev![pi-goals, rfl, eq-closure, nat-rec, app, binop] 
            exp![
            base!, 
            semistep!,
            recFn!] exp!{(thm!, 0)} 2 5000 =: `dist1
  let ⟨⟨base1, _⟩, ⟨semistep1, _⟩, ⟨recFn1, _⟩⟩ := seek
  let _ : semistep = semistep1 := by rfl
  let _ : base = base1 := by rfl
  let seek2 := evolve! ev![pi-goals, rfl, eq-closure, nat-rec, app, binop] 
            exp![ 
            base!, 
            semistep!,
            step!,
            recFn!] exp!{(thm!, 0), (semistep, 1)} 2 5000
  let seek3 := evolve! ev![Σev![simple-binop] ^ Σev![pi-goals]] exp![thm!] 
          exp!{(thm!, 0), (base, 0), (recFn, 0), (step, 0)} 2 5000
  let ⟨⟨thm, _⟩, _⟩ := seek3
  let pf : thm! := fun h => (recFn h) (base h) (step h)
  thm


#check localConst0
