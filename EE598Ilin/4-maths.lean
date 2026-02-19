import Mathlib

-- Feb 12
namespace lecture12

class Group (G : Type u) where
  op : G → G → G
  e : G
  inv : G → G
  -- properties
  assoc : op (op a b) c = op a (op b c)
  inv_left {a} : op (inv a) a = e
  id_left : op e a = a

class CommGroup (G : Type) extends Group G where
  comm : op a b = op b a

infixl:60 " + " => Group.op
prefix:95 "-" => Group.inv

open Group CommGroup

variable {G : Type} [Group G] {a b : G}
#check -(a + b) + a           -- G
#check a + b + e              -- G

theorem Group.id_inv_left {a : G}
  : e + (-a) = -a
  := by rw[id_left]

theorem Group.cancel_left : a + b = a + c → b = c := by
  intro h
  apply congrArg (fun t => -a + t) at h
  rw[←assoc] at h
  rw[inv_left] at h
  rw[id_left] at h
  rw[←assoc] at h
  rw[inv_left] at h
  rw[id_left] at h
  exact h

theorem Group.id_right : a + e = a := by
  apply cancel_left (a := -a)
  calc  -a +  (a + e)
  _   = (-a + a) + e   := by rw[assoc]
  _   = (e + e : G)    := by rw[inv_left]
  _   = e              := by rw[id_left]
  _   = -a + a         := by rw[inv_left]

theorem Group.id_unique {e' : G} : (∀ a, e'+ a = a) → e = e' := by
  intro h
  have : e' + e = e := h e
  symm
  rw[id_right] at this
  exact this

lemma Group.inv_right : a + -a = e := by
  apply cancel_left (a := -a)
  rw[← assoc,inv_left,id_left,id_right]

theorem Group.inv_unique : b + a = e → c + a = e → b = c := by
  intro h1 h2
  calc b = b + e := by rw[id_right]
       _ = b + (a + -a) := by rw[inv_right]
       _ = (b + a) + -a := by rw[assoc]
       _ = e + -a := by rw[h1]
       _ = (c + a) + -a := by rw[h2]
       _ = c + (a + -a) := by rw[assoc]
       _ = c + e := by rw[inv_right]
       _ = c := by rw[id_right]

instance Group.prod [Group G] [Group H] : Group (G × H) := {
  op x y := (x.1 + y.1, x.2 + y.2)
  e := (e,e)
  inv x := (-x.1, -x.2)
  assoc {x y z} := by simp[assoc]
  inv_left := by simp[inv_left]
  id_left := by simp[id_left]
}

end lecture12

namespace lecture13

inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

def Spin.neg : Spin → Spin
  | up => up
  | dn => dn

def op (x y : Spin) : Spin := match x, y with
  | up,dn => dn
  | dn,up => dn
  | _,_ => up

def Spin.mul (a b : Spin) : Spin :=
  match a, b with
  | dn, dn => dn
  | _, _ => up

instance Spin.Zero : Zero Spin := {
  zero := up
}
instance Spin.Add : Add Spin := {
  add := op
}

instance AddMonoid : AddMonoid Spin := {
  add := op
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  nsmul := nsmulRec
}

instance NegMonoid : Neg Spin := {
  neg := neg
}

instance Spin.inst_ring : Ring Spin := {
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  mul := mul
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one := dn
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  zsmul := zsmulRec
  neg_add_cancel := by intro a; cases a <;> rfl
}

theorem factor_mul_inv_right {x y : Spin} : x*(-y) = -(x*y) := by simp
example (x y : Spin) : x*y + x = x*(y+dn) := by
  cases x <;> cases y <;> exact rfl

instance Seq.inst_ring {R : Type u} [Ring R] : Ring (ℕ → R) := inferInstance
instance Seq.inst_group {R : Type u} [CommRing R] : CommRing (ℕ → R) := inferInstance

#check Ideal
#check NNReal
#check Subgroup

def Evens := Subtype (fun n => ∃ k, n = 2*k)
def Evens.add (x y : Evens) : Evens := ⟨x.1+y.1, by
  rcases x.2 with ⟨x', hx⟩
  rcases y.2 with ⟨y', hy⟩
  use x'+y'
  simp[hx,hy]
  ring⟩

def x : Fin 10 := 1
def y : Fin 10 := 2
#eval x+10*y
#eval (10:Fin 10)

def R : Finset ℚ := {1/2, 1/4, 1/8, 1/16}
#eval insert (4:ℚ) (insert (-4:ℚ) R)       --  {-4,-3,-2,-1,0,1,2,3,4}


end lecture13

namespace lecture14
#check True < False
#check List.lt

def te (σ₁ σ₂ : ℕ → α) : Prop := ∃ m, ∀ n > m, σ₁ n = σ₂ n

def Refl (R : α → α → Prop) := ∀ x, R x x

example :  Refl (Eq (α := α))         := fun _ => rfl
example :  Refl (te (α := α))         := fun _ => ⟨ 0, fun _ _ => rfl ⟩

example [hl : LT β] : ¬Refl (List.lt (α := β)) :=
  fun h => by simpa using (h [])

example [Preorder β] : Refl (List.le (α := β)) := by
  intro l
  induction l with
  | nil => exact List.not_lt_nil []
  | cons head tail ih =>
    intro h
    cases h with
    | rel h => exact (lt_self_iff_false head).mp h
    | cons h => exact ih h

example [Preorder β] : Refl (List.le (α := β)) := List.le_refl

-- quotients
def M (x y : ℤ) : Prop := ∃ k, x - y = 2*k

instance m_equiv : Equivalence M := {
  refl x        := by use 0; simp,
  symm {x y}    := by intro ⟨ k, hm ⟩; use -k; linarith,
  trans {x y z} := by intro ⟨ k, hk ⟩ ⟨ j, hj ⟩; use (k+j); linarith
}

instance m_setoid : Setoid ℤ := ⟨ M, m_equiv ⟩

abbrev Z2 := Quotient m_setoid

instance m_zero : Zero Z2 := ⟨ ⟦0⟧ ⟩

#check ⟦0⟧
#check ⟦2⟧
example : (⟦0⟧:Z2) = ⟦2⟧ := by
    apply Quotient.sound
    use -1
    simp

def pre_neg (x : ℤ) : Z2 := ⟦-x⟧

theorem pre_neg_respects : ∀ (a b : ℤ), a ≈ b → pre_neg a = pre_neg b := by
  intro a b ⟨ k, hk ⟩
  apply Quotient.sound
  use -k
  linarith

def Z2.neg (X : Z2) : Z2 := Quotient.lift pre_neg pre_neg_respects X

instance z2_neg : Neg Z2 := ⟨ Z2.neg ⟩

#check -(⟦3⟧:Z2)

end lecture14
