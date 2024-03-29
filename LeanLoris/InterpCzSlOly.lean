import LeanLoris.Evolution
import LeanLoris.Syntax
open Lean Meta Elab Term

namespace CzSlInterp

opaque M : Type

instance : Inhabited (M → M → M) := ⟨fun x _ => x⟩
opaque mul : M → M → M
noncomputable instance : Mul M := ⟨mul⟩

-- universe u
-- variable {M: Type u}[prod: Mul M]
-- def mul(m n: M) := m * n

elab "whnf#" e:term : term => do
  let e ← elabTerm e none
  logInfo m!"{e}"
  let e ← whnf e
  logInfo m!"{e}"
  Term.synthesizeSyntheticMVarsNoPostponing
  logInfo m!"{e}"
  pure e

variable (x y: M)

#check whnf# mul x y

example : (@instHMul M prod).1 = prod.1 := by rfl

@[simp] theorem mul_eq(a b : M) : mul a b = a * b := by rfl
/--
Our main model problem for forward reasoning is the following from a Czech-Slovak Olympiad:

Let `M` be a set with a product. Given the axioms:
* `∀ a b : M, (a * b) * b = a`
* `∀ a b : M, a * (a * b) = b`
then, for arbitrary elements `m` and `n` in `M`, we have `m * n = n * m`.

We fix `m` and `n` and reason forward starting with `m`, `n`, the axioms, and multiplication. Our forward reasoning is tuned for this problem, and also mildly help by including `m *n` in the initial state. But we do not use the statement of the problem, any of the lemmas or the proof.

To understand the (automated) reasoning steps (and for use during tuning and debugging), some lemmas and the theorem were defined. While running progress in proving these is logged.

* `def lem1! := (m * n) * n = m` 
* `def lem2! := (m * n) * ((m * n) * n) = n`
* `def lem3! := ((m * n) * m) * m = m * n`
* `def lem4! := (m * n) * ((m * n) * n) = (m * n) * m`
* `def lem5! := (m * n) * m = n`
* `def lem6! := ((m * n) * m) * m = n * m`
* `def thm! := m * n = n * m`

Running this is too resource intesive for the interpreter (but we have a compiled version that runs in `Main`). So here we cherry-pick the lemmas we want to use from the outputs of steps and use them as inputs for later steps.
-/
theorem CzSlOly : (∀ a b : M, (a * b) * b = a) → (∀ a b : M, a * (a * b) = b) →
            (m n: M) → m * n = n * m := by
              intros ax1 ax2 m n
              have lem1 : (m * n) * n = m := ax1 m n
              have lem2 : (m * n) * ((m * n) * n) = n := ax2 (m * n) n
              have lem3 : ((m * n) * m) * m = m * n  := ax1 (m * n) m
              have lem4 : (m * n) * ((m * n) * n) = (m * n) * m := 
                  congrArg (fun x => (m * n) * x) lem1              
              have lem5 : (m * n) * m = n := by
                    rw [lem4] at lem2
                    assumption
              have lem6 : ((m * n) * m) * m = n * m  := 
                    congrArg (fun x => x * m) lem5 
              rw [lem3] at lem6
              assumption 
set_option maxHeartbeats 100000000

-- set_option pp.all true

def CzSlInterpProof(ax1 : ∀ a b : M, (a * b) * b = a)(ax2 : ∀ a b : M, a * (a * b) = b)
                  (m n: M) := 
      let lem1! := (m * n) * n = m 
      let lem2! := (m * n) * ((m * n) * n) = n 
      let lem3! := ((m * n) * m) * m = m * n  
      let lem4! := (m * n) * ((m * n) * n) = (m * n) * m
      let lem5! := (m * n) * m = n
      let lem6! := ((m * n) * m) * m = n * m
      let thm! := m * n = n * m
      let step1a := evolve! ev![app, name-app, name-binop, binop] expr![lem1!, lem2!, lem3!] expr!{(ax1, 0), (ax2, 0), (m, 0), (n, 0), (m *n, 0)} name!{(mul, 0), (Eq, 0)} 3 6000
      let ⟨⟨lem1, _⟩, ⟨lem2, _⟩, ⟨lem3, _⟩, _⟩ := step1a
      let step1b := evolve! ev![congr-rec, name-binop] expr![lem4!] expr!{(m, 0), (n, 0), (m *n, 0), (lem1, 1), (lem2, 1), (lem3, 1)} name!{(CzSlInterp.mul, 0)} 3 6000
      let ⟨⟨lem4, _⟩, _⟩ := step1b
      let step2 := evolve! ev![eq-closure, name-binop] expr![lem5!] expr!{(m, 0), (n, 0), (m *n, 0),  (lem2, 1), (lem4, 3)} name!{(CzSlInterp.mul, 0)} 2 6000
      let ⟨⟨lem5, _⟩, _⟩ := step2
      let step3 := evolve! ev![congr-rec, name-binop] expr![lem6!] expr!{(m, 0), (n, 0), (m *n, 0), (lem5, 1)} name!{(CzSlInterp.mul, 0)} 3 6000
      let ⟨⟨lem6, _⟩, _⟩ := step3
      let step7 := evolve! ev![eq-closure, name-binop] expr![thm!] expr!{(m, 0), (n, 0), (m *n, 0),  (lem3, 1), (lem6, 1)} name!{(CzSlInterp.mul, 0)} 1 6000  
      let ⟨⟨thm, _⟩, _⟩ := step7                
      thm

#check @CzSlInterpProof

end CzSlInterp