import LeanLoris.Syntax 

set_option maxHeartbeats 100000000

def localConst{α : Type}(f: Nat → α) :=
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
            recFn!] exp!{(thm!, 0)} 2 5000 =: dist1
  let ⟨⟨base1, _⟩, ⟨semistep1, _⟩, ⟨recFn1, _⟩⟩ := seek
  let _ : semistep = semistep1 := by rfl
  let _ : base = base1 := by rfl
  let seek2 := evolve! ev![pi-goals, rfl, eq-closure, nat-rec, app, binop] 
            exp![ 
            base!, 
            semistep!,
            step!,
            recFn!] dist1 2 5000 =: dist2
  let seek3 := evolve! ev![Σev![simple-binop] ^ Σev![pi-goals]] exp![thm!] 
          exp!{(thm!, 0), (base, 0), (recFn, 0), (step, 0)} 2 5000
  let ⟨⟨thm, _⟩, _⟩ := seek3
  let pf : thm! := fun h => (recFn h) (base h) (step h)
  thm


#check localConst