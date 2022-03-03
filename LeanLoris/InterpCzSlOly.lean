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
                  let seek123 := evolve! ev![app, name-app] exp![lem1!, lem2!, lem3!] exp!{(ax1, 0), (ax2, 0), (m, 0), (n, 0)} name!{(mul, 0)} 5 1000
                  let seekmn := evolve! ev![app, name-app] exp![m * n] exp!{(m, 0), (n, 0)} name!{(mul, 0)} 5 1000
                  -- let seek123mn := evolve! ev![app, name-app, name-binop, binop] exp![lem1!, lem2!, lem3!] exp!{(ax1, 0), (ax2, 0), (m, 0), (n, 0), (m *n, 0)} !{(mul, 0), (Eq, 0)} 3 1000
                  -- let ⟨⟨lem1, w1⟩, ⟨lem2, w2⟩, ⟨lem3, w3⟩, _⟩ := seek123mn
                  let lem4! := (m * n) * ((m * n) * n) = (m * n) * m
                  let lem5! := (m * n) * m = n
                  -- let seek4 := evolve! ev![app, name-app, name-binop, eq-isles, binop] exp![lem1!, lem4!] exp!{(ax1, 0), (ax2, 0), (m, 0), (n, 0), (m *n, 0)} !{(mul, 0), (Eq, 0)} 4 2000
                  -- let ⟨_, ⟨lem4, w4⟩, _⟩ := seek4
                  -- let seek5 := evolve! ev![name-binop, eq-closure exp![n, (m * n) * ((m * n) * n)]] exp![m * n * n, (m * n) * ((m * n) * n), lem2!, lem4!, lem5!] exp!{(m, 0), (n, 0), (m *n, 0), (lem2, 1), (lem4, 3)} !{(mul, 0)} 4 2000
                  -- seek5
                  ()
             
#check @exploreProofs