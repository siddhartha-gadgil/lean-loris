open Nat

def slowFib (id : Nat) : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => dbgTrace s!"fib {id}" fun _ => slowFib id n + slowFib id (n+1)

-- def conc : Nat := 
--   let t1 := Task.spawn fun _ => slowFib 1 32
--   let t2 := Task.spawn fun _ => slowFib 2 32
--   let t3 := Task.spawn fun _ => slowFib 3 33
--   let t4 := Task.spawn fun _ => slowFib 4 34
--   t1.get + t2.get + t3.get + t4.get

-- #eval conc

def conc2 : Nat :=
  let arr := #[1, 3, 4, 5, 6]
  let tsks := arr.map fun n => Task.spawn fun _ => slowFib n (30 + n)
  let res := tsks.map fun t => t.get
  res.foldl (fun acc n => acc + n) 0

#eval conc2