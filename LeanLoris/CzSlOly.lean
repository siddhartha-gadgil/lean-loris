import LeanLoris.Evolution
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
set_option maxHeartbeats 10000000

def mul(m n: M) := m * n

def exploreProofs(ax1 : ∀ a b : M, (a * b) * b = a)(ax2 : ∀ a b : M, a * (a * b) = b)
                  (m n: M) := 
                  let lem1! := (m * n) * n = m 
                  let lem2! := (m * n) * ((m * n) * n) = n 
                  let lem3! := ((m * n) * m) * m = m * n  
                  let seek123 := evolve! ^[app, name-app] %[lem1!, lem2!, lem3!] %{(ax1, 0), (ax2, 0), (m, 0), (n, 0)} !{(mul, 0)} 5 1000
                  let seekmn := evolve! ^[app, name-app] %[m * n] %{(m, 0), (n, 0)} !{(mul, 0)} 5 1000
                  let seek123mn := evolve! ^[app, name-app, name-binop, binop] %[lem1!, lem2!, lem3!] %{(ax1, 0), (ax2, 0), (m, 0), (n, 0), (m *n, 0)} !{(mul, 0), (Eq, 0)} 5 1000
                  let lem4! := (m * n) * ((m * n) * n) = (m * n) * m
                  let lem4flip! := (m * n) * m = (m * n) * ((m * n) * n)
                  let lem5! := (m * n) * m = n
                  let seek4 := evolve! ^[app, name-app, name-binop, eq-isles, binop] %[lem1!, lem4!] %{(ax1, 0), (ax2, 0), (m, 0), (n, 0), (m *n, 0)} !{(mul, 0), (Eq, 0)} 4 2000
                  let seek5 := evolve! ^[app, name-app, name-binop, eq-isles, binop, eq-closure %[lem2!, lem4flip!, lem4!, lem5!]] %[lem2!, lem4!, lem4flip!, lem5!] %{(ax1, 0), (ax2, 0), (m, 0), (n, 0), (m *n, 0)} !{(mul, 0), (Eq, 0)} 6 3000
                  seek5
             
#check exploreProofs