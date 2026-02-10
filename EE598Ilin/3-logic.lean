import Mathlib

namespace lecture8

#check False
#check false

theorem t (p : Prop) : p ∨ ¬p :=
  Classical.em p

#print axioms t

example : p ∨ q → q ∨ p := fun hpq => match hpq with
  | Or.inl hl => Or.inr hl
  | Or.inr hr => Or.inl hr

theorem thm1 : (p∨q) ∧ (p∨r) → p ∨ (q∧r) := by
  rintro ⟨pq, pr⟩
  cases' pq with hp hq
  left
  exact hp
  cases' pr with hp hr
  left
  exact hp
  right
  exact ⟨hq, hr⟩

theorem thm2 : (p∨q) ∧ (p∨r) → p ∨ (q∧r) := fun ⟨pq, pr⟩ =>
  match pq with
  | Or.inl p => Or.inl p
  | Or.inr q =>
    match pr with
    | Or.inl p => Or.inl p
    | Or.inr r => Or.inr ⟨q, r⟩

#check thm1
#check thm2

example : p → ¬p → q :=
  fun hp hnotp => nomatch hnotp hp

-- how to see proof irrelevance?
example : @thm1 = @thm2 := rfl
example {P : Prop} (p1 p2 : P) : p1 = p2 := rfl

-- does this have a name?
example : (p → q) → p → q := fun f => f
example : (p → q) → p → q := (·)

variable (P Q : Prop)

example : P → P → P → P := fun p _ _ => p
example : (P → Q) → (¬Q → ¬P) := fun fpq notq p => notq (fpq p)
example : (P → Q) → (¬Q → ¬P) := fun fpq notq p => notq (fpq p)
example : ¬p → (p → q) := fun notp p => nomatch notp p
example : ¬p → (p → q) := (nomatch · ·)
example : (∀ x, x > 0) → (∀ y, y > 0) := fun p => p
example : (∀ x, x > 0) → (∀ y, y > 0) := (·)

def f : ℕ → ℕ := (·^2)

#check And

inductive And' (φ ψ : Prop) : Prop where
  | intro : φ → ψ → And' φ ψ

example (p q : Prop) : p → q → And' p q := And'.intro
example (p q : Prop) : p → q → And p q := And.intro


example {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by
  constructor
  · intro hpq hnq hp
    apply hnq
    apply hpq
    exact hp
  · intro h hp
    rcases Classical.em q with hq | hnq
    · exact hq
    · have := h hnq
      contradiction


example {p : Prop} : ((p → q) → p) → p := by
  contrapose
  intro h
  sorry



example : ((p → q) → p) → p := by
  rcases Classical.em p with hp | hnp
  · exact fun _ => hp
  · exact (· (nomatch hnp ·))

example {p : Prop} : ((p → q) → p) → p :=
  match Classical.em p with
  | Or.inl hp => fun _ => hp
  | Or.inr hnp => (· (nomatch hnp ·))

example {p : Prop} : ((p → q) → p) → p :=
  fun h => (Or.rec (fun hp => hp) (fun hnp => h (fun hp => nomatch hnp hp)) (Classical.em p))

example {p : Prop} : ((p → q) → p) → p :=
  fun h => (Or.recOn (Classical.em p) (fun hp => hp) (fun hnp => h (fun hp => nomatch hnp hp)))

example {p : Prop} : ((p → q) → p) → p :=
  fun h => (Or.recOn (Classical.em p) (·) (fun hnp => h (fun hp => nomatch hnp hp)))

example {p : Prop} : ((p → q) → p) → p :=
  fun h => (Or.recOn (Classical.em p) (·) (h fun hp => nomatch · hp))

example {p : Prop} : ((p → q) → p) → p :=
  fun h => (Or.recOn (Classical.em p) (·) (fun hnp => h (nomatch hnp ·)))

end lecture8

namespace lecture9

example : p ∧ (q ∧ r) → (p ∧ q) ∧ r := fun ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩
example : p ∧ (q ∧ r) → (p ∧ q) ∧ r := fun ⟨hp, hq, hr⟩ => ⟨⟨hp, hq⟩, hr⟩

example : False → True :=
  fun _ => trivial
example : False → True :=
  False.elim

def False.elim {p : Prop} (h : False) : p :=
  nomatch h
def False.elim' {p : Prop} (h : False) : p :=
  match h with.

#check Iff

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) :=
  ⟨fun ⟨pq, qp⟩ => ⟨pq, qp⟩, fun ⟨pq, qp⟩ => ⟨pq, qp⟩⟩

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

example : (p → q) → (¬p ∨ q) :=
  fun pq =>
    match Classical.em p with
    | .inl hp => Or.inr (pq hp)
    | .inr hnp => Or.inl hnp

inductive Person where
  | mary
  | steve
  | ed
  | jolin

open Person

def InSeattle (x : Person) : Prop := match x with
  | mary  | ed    => True
  | steve | jolin => False

#check InSeattle

#check id

example : InSeattle steve ∨ ¬InSeattle steve :=
  Or.inr (fun h => h) -- h is False
example : InSeattle steve ∨ ¬InSeattle steve :=
  Or.inr id

def is_zero (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ _ => False

#check is_zero

example : ¬is_zero 91 :=              -- is_zero 91 → False
  fun h => h -- h : False

def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

def on_left (p q : Person) : Prop := on_right q p

example : on_left mary jolin := by
  unfold on_left on_right
  exact Eq.refl mary

example : on_left mary jolin := Eq.refl _

#check rfl

example : p ∨ q ↔ q ∨ p :=
  ⟨fun h => match h with | Or.inl p => Or.inr p | Or.inr q => Or.inl q ,
  sorry⟩
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬(p ∧ ¬p) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry

end lecture9

-- Feb 5
namespace lecture10

variable {α : Type} (P Q : α → Prop)

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := fun hpq hp x => hpq x (hp x)

open lecture9 Person
example : ∃ x, on_right mary x := ⟨steve, Eq.refl _⟩
example : ∃ x, ¬on_right mary x := ⟨mary, sorry⟩

example : mary ≠ steve := fun h => nomatch h
example : mary ≠ steve := fun h => noConfusion h
theorem mary_not_steve : mary ≠ steve := fun h => by contradiction
#print mary_not_steve
#check noConfusion_of_Nat
#check noConfusionType

#eval Person.ctorIdx mary
#eval Person.ctorIdx steve
#eval Person.ctorIdx jolin

set_option pp.all true in
#print Nat.noConfusion
variable (p : Type → Prop) (q : Type → Prop) (r : Prop)
example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨fun h1 h2 => Exists.elim h2 h1,
   fun h1 x hp => h1 ⟨x, hp⟩⟩

#check Exists.elim

def i {α β γ} (f : α → β → γ) : β → α → γ := fun x y => f y x

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨i Exists.elim,
   fun h1 x hp => h1 ⟨x, hp⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  sorry

#help tactic

end lecture10

namespace lecture11

-- `reduce` tactic will beta-reduce
example : 9 = (3*(2+1)) := by
  reduce
  rfl
  -- apply Eq.refl

#check Eq.refl
#check Eq.subst

universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl a : MyEq a a

infix:50 " ~ "  => MyEq

theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
                   (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁ with
  | refl => exact h₂

theorem MyEq.congr_arg {α : Sort u} {a b : α} {f : α → α} : a ~ b → f a ~ f b := by
  intro hab
  apply MyEq.subst hab
  exact MyEq.refl (f a)

example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 :=
  fun h => MyEq.congr_arg (f := fun w => 2*w + 1) h

example (x y : Nat) (f := fun w => 2 * w + 1) : x ~ y → f x ~ f y :=
  fun h => MyEq.congr_arg h

theorem MyEq.to_iff (a b : Prop) : a ~ b → (a ↔ b) := by
  intro h
  cases h with
  | refl => rfl

example {a : Prop} : a ↔ a := Eq.to_iff rfl
example {a : Prop} : a ↔ a := Iff.of_eq rfl
example {a : Prop} : a = a := id_eq a
example {a : Prop} : a ↔ a := (id_eq a) ▸ Iff.rfl
example {a : Prop} : a ↔ a := Iff.rfl

theorem MyEq.to_iff' (a b : Prop) : a ~ b → (a ↔ b) := by
  intro h
  have : a ↔ a := Eq.to_iff rfl
  exact MyEq.subst h this

theorem MyEq.to_iff'' (a b : Prop) : a ~ b → (a ↔ b) := fun h => MyEq.subst h Iff.rfl

example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z := sorry

inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

postfix:95 " ⁻¹ " => toggle

#eval up⁻¹

@[simp] theorem toggle_up : up⁻¹ = dn := rfl
@[simp] theorem toggle_dn : dn⁻¹ = up := rfl

@[simp] theorem toggle_toggle {x} : x⁻¹⁻¹ = x := by
  cases x <;> simp  -- uses toggle_up, toggle_dn

@[simp] theorem toggle_toggle_toggle {x} :  x⁻¹⁻¹⁻¹ = x⁻¹ := by
  simp  -- uses toggle_up, toggle_dn

def op (x y : Spin) : Spin := match x, y with
  | up,dn => dn
  | dn,up => dn
  | _,_ => up

infix:75 " o " => op

@[simp] theorem op_up_left {x} : up o x = x := by cases x <;> rfl
@[simp] theorem op_up_right {x} : x o up = x := by cases x <;> rfl
@[simp] theorem op_dn_left {x} : dn o x = x⁻¹ := by cases x <;> rfl
@[simp] theorem op_dn_right {x} : x o dn = x⁻¹ := by cases x <;> rfl

@[simp] theorem toggle_op_left {x y} : (x o y)⁻¹ = x⁻¹ o y := by
  cases x <;> simp

#check mul_assoc

theorem assoc {x y z} : x o (y o z) = (x o y) o z := by cases x <;> simp

theorem com {x y} : x o y = y o x := by cases x <;> simp

theorem toggle_op_right {x y} : (x o y)⁻¹ = y o x⁻¹ := by cases x <;> simp

@[simp]
theorem inv_cancel_right {x} : x o x⁻¹ = dn := by cases x <;> simp

@[simp]
theorem inv_cancel_left {x} : x⁻¹ o x = dn := by cases x <;> simp

def S (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n + S x

example : ∀ n, 2 * S n = n*(n+1) := by
  intro n
  induction n with
  | zero => simp[S]
  | succ k ih =>
    simp[S]
    linarith         -- uses ih (check with clear ih before linarith)

theorem easy1 : S 0 = 0 := by simp[S]
theorem easy2 : S 0 = 0 := rfl
#print easy1
#print easy2

def T (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n*n + T x

example (n : ℕ) : 6 * (T n) = n * (n+1) * (2*n+1) := by
  induction n with
  | zero => simp[T]
  | succ m ih => grind[T]

example : up ≠ dn := by
  intro h
  nomatch h

inductive PreDyadic where
  | zero    : PreDyadic
  | add_one : PreDyadic → PreDyadic  -- x ↦ x + 1
  | half    : PreDyadic → PreDyadic  -- x ↦ x / 2
  | neg     : PreDyadic → PreDyadic  -- x ↦ -x

open PreDyadic

example (x : PreDyadic) : zero ≠ add_one x := fun h => nomatch h
example (x : PreDyadic) : zero ≠ add_one x := PreDyadic.noConfusion
example : ¬zero.add_one = zero.add_one.add_one.half := fun h => nomatch h
example : ¬zero.add_one = zero.add_one.add_one.half := PreDyadic.noConfusion

example (x y : PreDyadic) : add_one x = add_one y ↔ x = y := by
  constructor
  · intro h
    cases x <;> cases y <;> simp_all
  · intro h
    rw[h]

example (x y : PreDyadic) : add_one x = add_one y ↔ x = y :=
  ⟨fun h => by cases x <;> cases y <;> simp_all, fun h => congrArg add_one h⟩

structure Point (α : Type u) where
  x : α
  y : α

theorem Point.ext {α : Type} (p q : Point α) (hx : p.x = q.x) (hy : p.y = q.y)
  : p = q := by
  cases p; cases q;
  cases hx; cases hy;
  rfl

def shift (k x : ℤ) : ℤ := x+k

#check funext

@[simp]
theorem shift_inv_right {k} : shift k ∘ shift (-k) = id := by
  funext x              -- x : ℤ ⊢ (shift k ∘ shift (-k)) x = id x
  simp[shift]

@[simp]
theorem shift_inv_left {k} : shift (-k) ∘ shift k = id := by
  funext x
  simp[shift]

end lecture11
