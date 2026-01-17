-- Derrik's demo
import Mathlib
#check (Nat → Nat : Type)

namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat

def add' (m n : Nat) : Nat :=
  match m with
  | .zero => n
  | .succ m' => add' m' (Nat.succ n)

#eval add' (succ (succ zero)) (succ zero)

inductive List (A : Type) where
  | nil : List A
  | cons (head : A) (tail : List A) : List A

end Hidden

#check Nat
#check Nat.zero

open List

def append (xs ys : List A) : List A :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (append xs' ys)

def xs := [1,2,3]
def ys := [4,5,6]

#eval append xs ys

set_option trace.Meta.synthInstance true in
#check 4 ≤ 5
#check instLENat

inductive le (n : Nat) : Nat → Prop where
  | refl : le n n
  | step : le n m → le n (m+1)

theorem le_trans1 (a b c : Nat) (hab : le a b) (hbc : le b c) : le a c :=
  match hbc with
  | le.refl => hab
  | le.step hbc' => le.step (le_trans1 _ _ _ hab hbc')

theorem le_trans2 (a b c : Nat) (hab : le a b) (hbc : le b c) : le a c := by
  induction hbc with
  | refl => exact hab
  | step hbc' ih => exact le.step ih

theorem le_trans3 (a b c : Nat) (hab : le a b) (hbc : le b c) : le a c := by
  induction' hbc with c' hbc' hac'
  · exact hab
  · exact le.step hac'

theorem le_trans4 (a b c : Nat) (hab : le a b) (hbc : le b c) : le a c := by
  induction hbc
  · exact hab
  · rename_i a_ih
    exact le.step a_ih

