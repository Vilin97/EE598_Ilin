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

end lecture5

-- lecture 6
namespace lecture6

inductive A (n : Nat) : Type u where
  | a : A n

inductive B : Nat → Type u where
  | a : B n

#check A.rec
#check B.rec

-- ex 5
#check List.recOn

def length {α} (L : List α) : Nat :=
  List.recOn L 0 (fun h t mt => 1 + mt)

-- typeclasses
class Zero (α : Type) where
  zero : α

class Add (α : Type) where
  add : α → α → α

def sum {α : Type} (f : ℕ → α) (n : ℕ) [hz : Zero α] [ha : Add α] :=
  match n with
  | .zero => hz.zero
  | .succ k => ha.add (sum f k) (f n)

instance : Zero String where
  zero := ""

instance : Add String where
  add a b := a ++ b

#eval sum (fun n => String.singleton (Char.ofNat (n+96))) 26

#check (Add, Sub, Mul, Mod, Div, LT, LE)
#check (HAdd, HSub, HMul, HDiv)
#check Inhabited
#check Ord
#check LinearOrder
#check Coe
#check CommSemiring      -- adds theorems that interact with simplifier
#check Countable         -- adds theorems

inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x

open Dyadic

def double (y : Dyadic) :=
  match y with
    | .zero => zero
    | .add_one y' => add_one (add_one (double y'))
    | .half y' => y'
    | .neg y' => neg (double y')

-- x/2 + y = (x + y+y)/2
-- -x + y = -(x + -y)
def add (x y : Dyadic) :=
  match x with
  | zero => y
  | add_one x' => add x' (add_one y)
  | half x' => half (add x' (double y))
  | neg x' => neg (add x' (neg y))

def Dyadic.to_rat (x : Dyadic) : Rat :=
  match x with
  | .zero => 0
  | .add_one x' => 1 + x'.to_rat
  | .half x' => x'.to_rat / 2
  | .neg x' => -x'.to_rat

lemma to_rat_double (y : Dyadic) : (double y).to_rat = 2 * y.to_rat :=
  match y with
  | .zero => by simp [double, to_rat]
  | .add_one y' => by simp [double, to_rat, to_rat_double]; ring
  | .half y' => by simp [double, to_rat]; ring
  | .neg y' => by simp [double, to_rat, to_rat_double]

theorem to_rat_add (x y : Dyadic) : (add x y).to_rat = x.to_rat + y.to_rat :=
  match x with
  | .zero => by simp [add, to_rat]
  | .add_one x' => by rw [add, to_rat, to_rat_add, to_rat]; ring
  | .half x' => by rw [add, to_rat, to_rat_add, to_rat, to_rat_double]; ring
  | .neg x' => by simp [add, to_rat, to_rat_add, to_rat]; ring

def x := half (add_one zero) -- 1/2
def y := neg (add_one (add_one zero)) -- -2

#eval (add x y).to_rat = x.to_rat + y.to_rat

-- 0 * y = 0
-- (1 + x) * y = y + x * y
-- (x/2) * y = (x*y)/2
-- -x * y = - (x*y)
def Dyadic.mul (x y : Dyadic) :=
  match x with
  | .zero => zero
  | .add_one x' => add y (mul x' y)
  | .half x' => half (mul x' y)
  | .neg x' => neg (mul x' y)

theorem to_rat_mul (x y : Dyadic) : (mul x y).to_rat = x.to_rat * y.to_rat :=
  match x with
  | .zero => by simp [mul, to_rat]
  | .add_one x' => by rw [mul, to_rat, to_rat_add, to_rat_mul]; ring
  | .half x' => by rw [mul, to_rat, to_rat_mul, to_rat]; ring
  | .neg x' => by simp [mul, to_rat, to_rat_mul, to_rat]

#eval (mul x y).to_rat = x.to_rat * y.to_rat


-- instance : Zero Dyadic where
--   zero := zero

-- instance : One Dyadic where
--   one := add_one zero

-- instance : Add Dyadic where
--   add := add

-- instance : HAdd Dyadic Dyadic Dyadic where
--   hAdd := add

-- def x := add_one zero
-- def y := neg (half (add_one zero))
-- def z := add_one (add_one (neg (half (add_one zero))))

-- #eval toRat x
-- #eval toRat y
-- #eval toRat z

-- #eval toRat (x + y)
-- #eval toRat (x + z)

-- #eval toRat (x + y) = (toRat x) + (toRat y)
-- #eval toRat (x + z) = (toRat x) + (toRat z)
-- #eval toRat (y + z) = (toRat y) + (toRat z)

end lecture6
