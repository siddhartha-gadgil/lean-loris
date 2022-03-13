import LeanLoris.Syntax 

/-
Examples of simple proofs, which can readily run in the intepreter.
-/

namespace ElabExamples
/--
Our first example is one of the first abstract results one sees in algebra: given a multiplication on a set `α` with a left-identity `eₗ` and a right identity `eᵣ`, we have `eₗ = eᵣ`.

Our first proof is by forward reasoning using function application and equality closure under symmetry and transitivity.
-/
def left_right_identities1(α : Type)[Mul α](eₗ eᵣ: α)
      (idₗ : ∀ x : α, eₗ * x = x)(idᵣ : ∀ x: α, x * eᵣ = x) :=
        let thm! := eₗ = eᵣ 
        let directProof := evolve! ev![app, eq-closure] expr![thm!] 
                expr!{(idₗ, 0), (idᵣ, 0), (eₗ, 0), (eᵣ, 0)} 2 5000
        let ⟨⟨thm, _⟩, _⟩ := directProof
        thm 

def left_right_identities_backward(α : Type)[Mul α](eₗ eᵣ: α)
      (idₗ : ∀ x : α, eₗ * x = x)(idᵣ : ∀ x: α, x * eᵣ = x) : eₗ = eᵣ := by
        evolve ev![simple-app, eq-closure]  2 5000
      
#check left_right_identities1

/--
We give a second proof of the result: given a multiplication on a set `α` with a left-identity `eₗ` and a right identity `eᵣ`, we have `eₗ = eᵣ` to illustrate implicit "lemma choosing". Notice that the cutoff is just `1` for both steps. However the proof is obtained as during equality generation, we look-ahead and generate proofs of statements that are simple.

This example also illustrates saving the result of a step and loading in the next step.
-/
def left_right_identities2(α : Type)[Mul α](eₗ eᵣ: α)
      (idₗ : ∀ x : α, eₗ * x = x)(idᵣ : ∀ x: α, x * eᵣ = x) :=
        let thm! := eₗ = eᵣ 
        let lem1! := eₗ * eᵣ = eᵣ
        let lem2! := eₗ * eᵣ = eₗ
        let step1 := evolve! ev![app] expr![lem1!, lem2!] 
              expr!{(idₗ, 0), (idᵣ, 0), (eₗ, 0), (eᵣ, 0)} 1 1000 =: dist1
        let step2 := evolve! ev![eq-closure] expr![thm!] dist1 1 1000 
        let ⟨⟨thm, _⟩, _⟩ := step2
        thm 

#check left_right_identities2 

/--
We prove modus-ponens using mixed reasoning, specifically function application and introduction of variables for domains of goals.
-/
def modus_ponens(A B: Prop) :=
  let mp := A → (A → B)→ B
  let ⟨⟨thm, _⟩, _⟩ := 
      evolve! ev![intro, simple-app] expr![mp] expr!{(mp, 0)} 1 1000
  thm

#check modus_ponens

/-
The below examples are elementary. 
-/

-- ∀ (A : Prop), A → A
def implies_self(A: Prop) :=
  let idA := ∀ a : A, A
  let ⟨⟨thm, _⟩, _⟩ := evolve! ev![intro-all] expr![idA] expr!{(idA, 0)} 1 1000
  thm

#check implies_self

-- ∀ (A B : Prop), A → (A → B) → B
def deduction(A B: Prop)(a : A)(f: A → B) :=
  let ⟨⟨thm, _⟩, _⟩ := evolve! ev![simple-app] expr![B] expr!{(f, 0), (a, 0)} 1 10000
  thm

#check deduction

-- ∀ (A : Type) (a : A), a = a
def eql_refl(A: Type) :=
  let p := ∀ a: A, a = a
  let ⟨⟨thm, _⟩, _⟩ := evolve! ev![intro, rfl] expr![p] expr!{(p, 0)} 1 
  thm

#check eql_refl

-- ∀ (a b c : Nat), a = b → a = c → b = c
def eql_flip_trans(a b c: Nat)(p: a = b)(q: a = c) :=
    let ⟨⟨thm, _⟩, _⟩ := evolve! ev![eq-closure] expr![b = c, b = a, a = b] expr!{(p, 0), (q, 0)} 1 1000
    thm

#check eql_flip_trans

end ElabExamples

namespace TacticExamples

/--
Our first example is one of the first abstract results one sees in algebra: given a multiplication on a set `α` with a left-identity `eₗ` and a right identity `eᵣ`, we have `eₗ = eᵣ`.

Our first proof is by forward reasoning using function application and equality closure under symmetry and transitivity.
-/
def left_right_identities1(α : Type)[Mul α](eₗ eᵣ: α)
    (idₗ : ∀ x : α, eₗ * x = x)(idᵣ : ∀ x: α, x * eᵣ = x) : eₗ = eᵣ := 
      by
        evolve ev![simple-app, eq-closure]  2 

/--
We give a second proof of the result: given a multiplication on a set `α` with a left-identity `eₗ` and a right identity `eᵣ`, we have `eₗ = eᵣ` to illustrate implicit "lemma choosing". Notice that the cutoff is just `1` for both steps. However the proof is obtained as during equality generation, we look-ahead and generate proofs of statements that are simple.

This example also illustrates saving the result of a step and loading in the next step.
-/
def left_right_identities2(α : Type)[Mul α](eₗ eᵣ: α)
    (idₗ : ∀ x : α, eₗ * x = x)(idᵣ : ∀ x: α, x * eᵣ = x) : eₗ = eᵣ:= by
        evolve ev![app] 1  =: dist1
        evolve ev![eq-closure] dist1 1  

/--
We prove modus-ponens using mixed reasoning, specifically function application and introduction of variables for domains of goals.
-/
def modus_ponens(A B: Prop) : A → (A → B)→ B := by
  evolve ev![intro, simple-app] 1 

def modus_ponens2(A B: Prop) : A → (A → B)→ B := by
  intros
  evolve ev![simple-app] 1

/-
The below examples are elementary. 
-/

-- ∀ (A : Prop), A → A
def implies_self(A: Prop) : A → A := by
  evolve ev![intro-all]  1 

-- ∀ (A B : Prop), A → (A → B) → B
def deduction(A B: Prop)(a : A)(f: A → B) : B := by
  evolve ev![simple-app]  1 

-- ∀ (A : Type) (a : A), a = a
def eql_refl(A: Type) : ∀ a: A, a = a := by
  evolve ev![intro, rfl]  1

-- ∀ (a b c : Nat), a = b → a = c → b = c
def eql_flip_trans(a b c: Nat)(p: a = b)(q: a = c) : b = c := by
    evolve ev![eq-closure]  1 

#check eql_flip_trans


end TacticExamples