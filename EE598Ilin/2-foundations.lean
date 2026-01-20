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

-- lecture 5
namespace lecture5

-- ex 1
def f1 : α → (α → α) := fun (x : α) => (fun _ => x)
def f2 : (Type → Type) → Type := fun (_ : Type → Type) => Prop

#check fun x y => x + y
#check_failure fun g y => g y
#check fun (g : Type → Type) y => g y

-- ex 4
variable (x : ℕ)
-- size x = 1

def f : ℕ → (ℕ → ℕ) := fun x => (fun _ => x)
-- size f = 1 + size (fun _ => x) = 1 + (1 + 1) = 3

#check f x
-- size f x = 1 + size x + size f = 1 + 1 + 3 = 5

def α := Type
def c₂ := fun ( f : α → α ) => fun x => f (f x)
def c₃ := fun ( f : α → α ) => fun x => f (f (f x))
#check c₂
def N := (α → α) → α → α -- the type of Church numerals

-- ex 5
def double (a : N) : N := fun f => fun x => a f (a f x)
#reduce double c₂
#reduce (types := true) double c₂
#reduce double fun ( f : α → α ) => fun x => f (f x)
#reduce (types := true) double c₃

lemma lem1 (p q : Prop) : p → (p → q) → q :=
  fun hp => fun hpq => hpq hp

#print lem1

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons {n} :  α → Vec α n → Vec α (n + 1)

-- ex 1
structure Pair (α β : Type) where
  left : α
  right : β

--ex 2
-- def swap := fun (p : Pair) => Pair.mk p.right p.left
def swap {α β : Type} := fun (p : Pair α β) => Pair.mk p.right p.left

#check swap

-- ex 3
def chooseType : Bool → Type
| true  => Nat
| false => String

-- def f_fun : (b : Bool) → chooseType b := fun (b : Bool) => (if b then (0 : Nat) else "")
def f_fun' : (b : Bool) → chooseType b := fun (b : Bool) =>
  match b with
  | true => (0 : Nat)
  | false => ""
