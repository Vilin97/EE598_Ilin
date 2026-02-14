import Mathlib

namespace dyadic

-- k/2^n
inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x

open Dyadic


example (x y : Dyadic) : add_one x = add_one y ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    simp[h]

example (x y : Dyadic) : add_one x = add_one y ↔ x = y :=
  ⟨(add_one.noConfusion · id), congr_arg add_one⟩

#check Eq.refl

lemma add_one_inj (x y : Dyadic) (h : add_one x = add_one y) :  x = y := by
  cases h
  rfl

example (x y : Dyadic) (h : add_one x = add_one y) :  x = y := by
  cases x <;> cases y <;> cases h <;> rfl

example (x y : Dyadic) (h : add_one x = add_one y) :  x = y := by
  cases x <;> cases y <;> simp_all

example (x y : Dyadic) (h : add_one x = add_one y) :  x = y := by
  cases x <;> cases y <;> try?

example (x y : Dyadic) (h : add_one x = add_one y) :  x = y := add_one.noConfusion h id

#print add_one_inj
#check add_one.noConfusion

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

def Dyadic.repr : Dyadic → Std.Format
  | .zero => "zero"
  | .add_one x => "add_one (" ++ x.repr ++ ")"
  | .half x => "half (" ++ x.repr ++ ")"
  | .neg x => "neg (" ++ x.repr ++ ")"

instance : Repr Dyadic where
  reprPrec d _ := d.repr

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

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)

def num_half (x : Dyadic) : ℕ :=
  match x with
  | .zero => 0
  | .add_one y => num_half y
  | .half y => 1 + num_half y
  | .neg y => num_half y

def num_constr (x : Dyadic) : ℕ :=
  match x with
  | .zero => 0
  | .add_one y => 1 + num_constr y
  | .half y => 1 + num_constr y
  | .neg y => 1 + num_constr y

-- y/2 - 1 = (y-2)/2
-- -y - 1 = -(y+1)
-- partial
def sub_one (x : Dyadic) :=
  match x with
  | .zero => neg (add_one zero)
  | .add_one y => y
  | .half y => half (add y (neg (add_one (add_one zero))))
  | .neg y => neg (add_one y)

def x0 := zero
def x1 := half zero
def x2 := half (half zero)
#eval x0
#eval x1
#eval (sub_one x0)
#eval (sub_one x1)
#eval (sub_one x2)

lemma sub_add (x : Dyadic) : sub_one (add_one x) = x := by
  rfl

lemma add_one_inj' (x y : Dyadic) (h : add_one x = add_one y) :  x = y := by
  rw[←sub_add x, ←sub_add y, h]

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

-- True when x has no neg constructors used to define it.
def negs (x : Dyadic) : Prop :=
  match x with
  | .zero => False
  | .add_one y => negs y
  | .half y => negs y
  | .neg _ => True

def no_negs (x : Dyadic) : Prop := ¬negs x

instance instNegsDecidable (x : Dyadic) : Decidable (negs x) :=
  match x with
  | .zero => Decidable.isFalse (fun h => nomatch h)
  | .add_one x' => instNegsDecidable x'
  | .half x' => instNegsDecidable x'
  | .neg _ => Decidable.isTrue trivial

#eval y
set_option diagnostics true in
#eval negs y

theorem neg_double (x : Dyadic) : negs x → negs (double x) :=
  fun h =>
    match x with
    | .zero => h
    | .add_one x' => neg_double x' h
    | .half _ => h
    | .neg _ => h

theorem no_negs_double (x : Dyadic) : no_negs x → no_negs (double x) := by
  cases x with
  | zero => exact (·)
  | add_one x' => exact no_negs_double x'
  | half x' => exact fun h => h
  | neg x' => exact fun h => by rw[no_negs, negs] at h; nomatch h

example (x : Dyadic) : no_negs x → no_negs (double x) :=
  Dyadic.recOn x
    (·)
    (fun x' h => h)
    (fun x' h h' => h')
    (fun x' h h' => by rw[no_negs, negs] at h'; nomatch h')

example : double ∘ half = id := by
  ext x
  rfl

end dyadic
