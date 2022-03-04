import LeanLoris.Evolution
import LeanLoris.Syntax
universe u

variable {M: Type u}[Mul M]

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

def mul(m n: M) := m * n

def exploreProofs(ax1 : ∀ a b : M, (a * b) * b = a)(ax2 : ∀ a b : M, a * (a * b) = b)
                  (m n: M) := 
                  let lem1! := (m * n) * n = m 
                  let lem2! := (m * n) * ((m * n) * n) = n 
                  let lem3! := ((m * n) * m) * m = m * n  
                  let lem4! := (m * n) * ((m * n) * n) = (m * n) * m
                  let lem5! := (m * n) * m = n
                  let lem6! := ((m * n) * m) * m = n * m
                  let thm! := m * n = n * m
                  let step1a := evolve! ev![app, name-app, name-binop, binop] exp![lem1!, lem2!, lem3!] exp!{(ax1, 0), (ax2, 0), (m, 0), (n, 0), (m *n, 0)} name!{(mul, 0), (Eq, 0)} 3 6000
                  let ⟨⟨lem1, w1⟩, ⟨lem2, w2⟩, ⟨lem3, w3⟩, _⟩ := step1a
                  let step1b := evolve! ev![eq-isles, name-binop] exp![lem4!] exp!{(m, 0), (n, 0), (m *n, 0), (lem1, 1), (lem2, 1), (lem3, 1)} name!{(mul, 0)} 3 6000
                  let ⟨⟨lem4, w4⟩, _⟩ := step1b
                  let step2 := evolve! ev![eq-closure, name-binop] exp![lem5!] exp!{(m, 0), (n, 0), (m *n, 0),  (lem2, 1), (lem4, 3)} name!{(mul, 0)} 2 6000
                  let ⟨⟨lem5, w5⟩, _⟩ := step2
                  let step3 := evolve! ev![eq-isles, name-binop] exp![lem6!] exp!{(m, 0), (n, 0), (m *n, 0), (lem5, 1)} name!{(mul, 0)} 3 6000
                  let ⟨⟨lem6, w6⟩, _⟩ := step3
                  let step7 := evolve! ev![eq-closure, name-binop] exp![thm!] exp!{(m, 0), (n, 0), (m *n, 0),  (lem3, 1), (lem6, 1)} name!{(mul, 0)} 1 6000  
                  let ⟨⟨thm, w7⟩, _⟩ := step7                
                  thm

#check @exploreProofs