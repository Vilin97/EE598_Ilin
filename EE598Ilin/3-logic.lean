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

variable (P Q : Prop)

example : P → P → P → P := fun p _ _ => p
example : (P → Q) → (¬Q → ¬P) := fun fpq notq p => notq (fpq p)
example : ¬p → (p → q) := fun notp p => nomatch notp p
example : (∀ x, x > 0) → (∀ y, y > 0) := fun p => p

#check And

inductive And' (φ ψ : Prop) : Prop where
  | intro : φ → ψ → And' φ ψ

example (p q : Prop) : p → q → And' p q := And'.intro
example (p q : Prop) : p → q → And p q := And.intro

end lecture8
