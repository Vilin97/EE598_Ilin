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

def fibAux (n : ℕ) (a b : ℕ) : ℕ := match n with
  | 0 => a
  | k+1 => fibAux k b (a+b)
def fib'' (n : ℕ) := fibAux n 1 1
#eval fib'' 5

#eval fib 30
#eval fib'' 70000

example : fib 6 = fib 6 := by
  unfold fib
  unfold fib
  unfold fib
  sorry

example : fib'' 6 = fib'' 6 := by
  unfold fib''
  unfold fibAux
  unfold fibAux
  sorry

-- Ex 5
def mediant (x y : ℚ) := (x.num + y.num) / (x.den + y.den)

-- lecture 3
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat.zero
#check MyNat.succ
#check MyNat.succ MyNat.zero

inductive MyNat' where
  | zero : MyNat'
  | succ (n : MyNat') : MyNat'

inductive MyComplex where
  | mk (re : ℝ) (im : ℝ) : MyComplex

def MyComplex.re (z : MyComplex) : ℝ :=
  match z with
  | MyComplex.mk re im => re

inductive TriBool where
  | T : TriBool
  | F : TriBool
  | U : TriBool -- undefined

open TriBool

def and (A B : TriBool) :=
  match A, B with
  | T, T => T
  | T, F => F
  | F, T => F
  | F, F => F
  | _, _ => U

def first (L : List α) : Option α :=
  match L with
  | [] => Option.none
  | x::_ => x -- x is coerced from α to Option α via x ↦ Option.some x

#eval first ([] : List ℕ)
#eval first [1]

def first_plus_one (L : List ℕ) : Option ℕ :=
  let x := first L
  match x with
  | .none => .none
  | .some n => n + (1:ℕ)

-- Ex 1
inductive polarComplex where
  | mk (r : ℝ) (θ : ℝ) : polarComplex

inductive BTree (α : Type) where
  | leaf (v : α) : BTree α
  | node (v : α) (left : BTree α) (right : BTree α) : BTree α

namespace BTree
#check leaf 1
#check node 1 (leaf 0) (leaf 2)

def my_tree := node 1 (leaf 2) (node 3 (leaf 4) (leaf 5))

#eval my_tree

def to_str [h : ToString α] (T : BTree α) :=
  match T with
  | leaf a => toString a
  | node a L R => "(" ++ toString a ++ " " ++ to_str L ++ " " ++ to_str R ++ ")"

#eval to_str my_tree

instance [Repr α] [ToString α] : Repr (BTree α) := {
  reprPrec := fun T _ => to_str T
}

#eval my_tree

-- Ex 4
def swap (T : BTree α) : BTree α :=
  match T with
  | leaf v => leaf v
  | node v L R => node v (swap R) (swap L)

#eval swap my_tree

end BTree

-- mutual induction
mutual
  inductive Ev where
  | zero : Ev
  | succ : Od → Ev

  inductive Od where
  | succ : Ev → Od
end

mutual
    inductive Term
    | var : String → Term
    | num : ℕ → Term
    | paren : Expr → Term

    inductive Expr
    | neg : Term → Expr
    | add : Term → Term → Expr
    | mul : Term → Term → Expr
end

open Expr Term

def expr : Expr := mul (num 2) (paren (add (var "x") (num 1)))

-- Ex 5, count additions in an expression
mutual
  def Term.CountAdds (t : Term) : ℕ :=
    match t with
    | var s => 0
    | num n => 0
    | paren e => e.CountAdds

  def Expr.CountAdds (e : Expr) : ℕ :=
    match e with
    | neg t => t.CountAdds
    | add t1 t2 => 1 + t1.CountAdds + t2.CountAdds
    | mul t1 t2 => t1.CountAdds + t2.CountAdds
end

#eval expr.CountAdds

-- structures
-- this is syntactic sugar for `inductive MyComplex where | mk (re : ℝ) (im : ℝ) : MyComplex`
structure Komplex where
  re : Real
  im : Real

open Komplex

def conj (x : Komplex) := Komplex.mk x.re (-x.im)

-- several ways to unpack data from a structure
def negate1 (x : Komplex) : Komplex :=
  match x with | mk a b => ⟨ -a, -b ⟩

def negate2 (x : Komplex) : Komplex :=
  match x with | ⟨ a, b ⟩ => ⟨ -a, -b ⟩

def negate3 (x : Komplex) : Komplex :=
  let ⟨ a, b ⟩ := x
  ⟨ -a, -b ⟩

def negate4 (x : Komplex) : Komplex := ⟨ -x.1, -x.2 ⟩

-- fields in a structure can use previous fields
structure Dyn where
  α : Type
  a : α

structure Node where
  label : String
  next : Option Node

def chain : Node := {
    label := "a"
    next := some { label := "b", next := none }
}

#eval chain
#check ℕ × ℕ × ℕ

-- Π types
def Qn := Π _ : ℕ, ℚ
-- dependent type
def DPT := Π n : ℕ, Fin (n+1)
def DPT' := (n : ℕ) → Fin (n+1)

def σ1 : DPT := fun n => ⟨n, by lia⟩

-- Ex 9
def Shape := ℝ ⊕ (ℝ × ℝ)


noncomputable
def area (s : Shape) : ℝ :=
  match s with
  | .inl r => Real.pi * r*r
  | .inr ⟨x, y⟩ => x * y

def MyNat.add (x y : MyNat) :=
  match x with
  | .zero => y
  | .succ k => .succ (MyNat.add k y)

def MyNat.add_twice (x y : MyNat) :=
  match x with
  | .zero => y
  | .succ k => .succ (.succ (MyNat.add_twice k y))

infix:65 " + " => MyNat.add
infix:65 " ++ " => MyNat.add_twice

-- NOTE: This does not work:
-- #eval MyNat.zero.succ + MyNat.zero + MyNat.zero
#eval MyNat.zero.succ ++ MyNat.zero
-- #eval MyNat.zero.succ ++ MyNat.zero.succ + MyNat.zero

-- Ex 13
namespace Temp

inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x

/-
a. Define Dyadic.double that doubles a Dyadic.
b. Define Dyadic.add that adds two Dyadic values.
c. Define Dyadic.mul that multiplies two Dyadic values.
d. Define a function Dyadic.to_rat that converts a Dyadic to a Rat.
e. Define the Dyadics 5/8 and -7/32 and test your methods on these values.
f. Are Dyadics as defined here unique? Why or why not?
-/
