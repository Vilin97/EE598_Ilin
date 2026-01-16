-- lecture 4
import Mathlib

#check fun _ => 1
#check λ _ => 1
#check λ _ ↦ 1

def test : A → A := λ x ↦ x

-- Ex 2
def h := fun (x : ℕ) => x^2

#eval h (h (h 2))
#reduce h (h (h 2))

-- Ex 4, does not work in simply typed lambda calculus:
-- def Ω {A : Type} := λ (x : A → A) => x x

#check_failure Type 100

universe u
variable (n : Nat)
-- #check Type (u+n) -- does not work
#check Prop
#check Type*

def f2.{w} (x : Type w) : Type w := x
#check f2
#check f2 Nat

#check Type 2 → Type 7       -- Type 1
