import LeanLoris.Syntax 

def implies_self(A: Prop) :=
  let idA := ∀ a : A, A
  let ⟨⟨thm, _⟩, _⟩ := evolve! ev![pi-goals-all] exp![idA] exp!{(idA, 0)} 1 1000
  thm

#check implies_self

def deduction(A B: Prop)(a : A)(f: A → B) :=
  let ⟨⟨thm, _⟩, _⟩ := evolve! ev![app] exp![B] exp!{(f, 0), (a, 0)} 1 1000
  thm

#check deduction

def eql_refl(A: Type) :=
  let p := ∀ a: A, a = a
  let ⟨⟨thm, _⟩, _⟩ := evolve! ev![pi-goals, rfl] exp![p] exp!{(p, 0)} 1 1000
  thm

#check eql_refl

def eql_flip_trans(a b c: Nat)(p: a = b)(q: a = c) :=
    let ⟨⟨thm, _⟩, _⟩ := evolve! ev![eq-closure] exp![b = c, b = a, a = b] exp!{(p, 0), (q, 0)} 1 1000
    thm

#check eql_flip_trans

def modus_ponens(A B: Prop) :=
  let mp := A → (A → B)→ B
  let ⟨⟨thm, _⟩, _⟩ := 
      evolve! ev![pi-goals, simple-app] exp![mp] exp!{(mp, 0)} 1 1000
  thm

#check modus_ponens

def left_right_identities(α : Type)[Mul α](eₗ eᵣ: α)
      (idₗ : ∀ x : α, eₗ * x = x)(idᵣ : ∀ x: α, x * eᵣ = x) :=
        let thm! := eₗ = eᵣ 
        let directProof := evolve! ev![app, eq-closure] exp![thm!] 
                exp!{(idₗ, 0), (idᵣ, 0), (eₗ, 0), (eᵣ, 0)} 2 5000
        let ⟨⟨pf, _⟩, _⟩ := directProof
        have _ : thm! := pf
        let lem1! := eₗ * eᵣ = eᵣ
        let lem2! := eₗ * eᵣ = eₗ
        let step1 := evolve! ev![app] exp![lem1!, lem2!] 
              exp!{(idₗ, 0), (idᵣ, 0), (eₗ, 0), (eᵣ, 0)} 1 1000 =: dist1
        let step2 := evolve! ev![eq-closure] exp![thm!] dist1 1 1000 
        let ⟨⟨thm, _⟩, _⟩ := step2
        thm 

#check left_right_identities 
