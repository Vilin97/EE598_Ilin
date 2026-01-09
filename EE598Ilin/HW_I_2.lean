import Mathlib

-- lecture 1
#eval 1+1

example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : 12*y - 4*z < 0) : False := by
  linarith

theorem T₁ : ∀ x : ℝ , 0 ≤ x^2 := sorry

#check 1
#check "1"
#check T₁
#check ∀ (x : ℝ), 0 ≤ x ^ 2
#check Prop
#check Type


#eval 2+2
#eval Nat.Prime 741011

example : p → p := fun p => p

-- theorem myTheorem : p → p := fun p => p

theorem myTheoremTwo {p : Prop} : p → p := fun p => p

def remove_zeros (L : List ℕ) : List ℕ := match L with
  | [] => []
  | x::Q => if x = 0 then remove_zeros Q else x :: remove_zeros Q

#check remove_zeros
#eval remove_zeros [0,1,2,0,3,0,0,4]

def square_list (L : List ℕ) : List ℕ := match L with
  | [] => []
  | x::Q => x^2 :: square_list Q

#eval square_list [0,1,2,3]

def my_gcd (n m : ℕ) : ℕ :=
  if h : m = 0 then n else my_gcd m (n % m)
  termination_by m
  decreasing_by
    exact Nat.mod_lt n (Nat.pos_of_ne_zero h)

#eval my_gcd 48 18
#eval my_gcd 123456 789012 = gcd 123456 789012
#eval my_gcd 100 0
#eval gcd 100 0

example (n m : ℕ) (h : ¬m = 0) : n % m < m := by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero h)

#eval List.find? (fun x => x>0) [-1, 0, 1, 4, 0, 5]

example : [-1, 0, 1].find? (· ≥ 1) = some 1 := by
  rfl

-- lecture 2

def f1 (x : ℕ) : ℕ := x+1
#eval f1 1

def f2 := fun x => if x < 10 then 0 else 1
#eval f2 5
#eval f2 15

def f3 (x : ℕ) : ℕ :=
  let y := x*x
  y+1

#eval f3 4
#eval (let x := 5; x*2) + (let x := 3; x-1)

def f4 (x y : ℕ) := 2*x + y
#eval f4 1 2
#eval (f4 1) 2 -- partial application

def do_twice (f : ℕ → ℕ) (x : ℕ) := f (f x)
#eval do_twice f1 3

example : do_twice (do_twice f1) 3 = 7 := by
  unfold f1 do_twice
  rfl

def h1 (_ : ℕ) := 1
def h2 (_x : ℕ) := 1

def abs_diff (x y : ℕ) := if x > y then x-y else y-x
#eval abs_diff 23 89
#eval abs_diff 101 89

def apply_twice_when_even (f : ℕ → ℕ) (x : ℕ) :=
  if Even x then f (f x) else f x

#eval apply_twice_when_even (abs_diff 10) 8
#eval apply_twice_when_even (abs_diff 10) 11

theorem abs_diff_symm : abs_diff x y = abs_diff y x := by
  unfold abs_diff
  aesop
  linarith

#print Nat

-- pattern matching:
def nonzero (x : ℕ) : Bool := match x with
  | Nat.zero => false
  | Nat.succ _ => true

def is_3_or_12 (x : ℕ) := match x with
  | 3 => true
  | 12 => true
  | _ => false

def is_3_and_12 (x y : ℕ) := match x, y with
  | 3, 12 => true
  | _, _ => false

def factorial (n : ℕ) : ℕ := match n with
  | 0 => 1
  | k+1 => n * factorial k

#eval factorial 4

def do_n' (n : ℕ) (f : α → α) (x : α) := match n with
  | 0 => x
  | k+1 => f (do_n' k f x)

#eval do_n' 10 f1 0

partial def not_ok (x : ℕ) : ℕ := not_ok x

-- make factorial O(1) in memory
def factAux (n acc : ℕ) := match n with
  | 0 => acc
  | k+1 => factAux k (acc * (k+1))

def factorial' (n : ℕ) := factAux n 1

def factorial'' (n : ℕ) :=
  let rec aux (n acc : ℕ) := match n with
    | 0 => acc
    | k+1 => aux k (acc * (k + 1))
  aux n 1

-- O(2^n) runtime and memory
def fib (n : ℕ) := match n with
  | 0 => 1
  | 1 => 1
  | k+2 => fib k + fib (k+1)

#eval fib 4
#eval fib 5

example : fib 6 = fib 6 := by
  unfold fib
  unfold fib
  unfold fib
  unfold fib
  sorry

def do_n (n : ℕ) (f : α → α) (x : α) := match n with
  | 0 => x
  | k+1 => f (do_n k f x)
def fib_step : ℕ × ℕ → ℕ × ℕ := fun (n,m) => (m, n+m)
def fib' (n : ℕ) := (do_n n fib_step (1,1)).1

example : fib' 6 = fib' 6 := by
  unfold fib'
  unfold do_n
  unfold fib_step
  unfold fib
  sorry

-- Ex 5
def mediant (x y : ℚ) := (x.num + y.num) / (x.den + y.den)
