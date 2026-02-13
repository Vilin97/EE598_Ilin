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
