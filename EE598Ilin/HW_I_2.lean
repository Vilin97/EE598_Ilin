import Mathlib

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

def euclidean_alg (n m : ℕ) : ℕ :=
  if h : m = 0 then n else euclidean_alg m (n % m)
  termination_by m
  decreasing_by
    exact Nat.mod_lt n (Nat.pos_of_ne_zero h)

example (n m : ℕ) (h : ¬m = 0) : n % m < m := by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero h)

#eval List.find? (fun x => x>0) [-1, 0, 1, 4, 0, 5]

example : [-1, 0, 1].find? (· ≥ 1) = some 1 := by
  rfl
