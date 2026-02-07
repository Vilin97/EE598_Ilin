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
