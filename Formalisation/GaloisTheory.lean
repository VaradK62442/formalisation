-- Galois Theory - 2025/26
--
-- Definitions, Theorems, Exercises

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

import Formalisation.Algebra

namespace GaloisTheory

variable {α : Type} {X : Set α} {add mul : α → α → α}
variable {β : Type} {X' : Set β} {add' mul' : β → β → β}

structure Ring (X : Set α) (add mul : α → α → α) where
  one : α
  additive_group : Algebra.Group X add
  abelian_group : Algebra.isAbelian additive_group
  id_mem : one ∈ X
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_id : ∀ a, mul one a = a ∧ mul a one = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)


lemma mulId (R : Ring X add mul) :
  ∀ a, mul a R.additive_group.id = R.additive_group.id
  ∧ mul R.additive_group.id a = R.additive_group.id := by
    intro a
    constructor
    · have h := calc
        mul a R.additive_group.id = mul a (add R.additive_group.id R.additive_group.id) := by
          rw [(R.additive_group.op_id R.additive_group.id).left]
        _ = add (mul a R.additive_group.id) (mul a R.additive_group.id) := by
          rw [R.left_distrib]
      nth_rewrite 1 [←(R.additive_group.op_id (mul a R.additive_group.id)).right] at h
      rw [
        ←Algebra.groupLCancel R.additive_group
        R.additive_group.id
        (mul a R.additive_group.id)
        (mul a R.additive_group.id)
      ]
      exact h
    · have h := calc
        mul R.additive_group.id a = mul (add R.additive_group.id R.additive_group.id) a := by
          rw [(R.additive_group.op_id R.additive_group.id).right]
        _ = add (mul R.additive_group.id a) (mul R.additive_group.id a) := by
          rw [R.right_distrib]
      nth_rewrite 1 [←(R.additive_group.op_id (mul R.additive_group.id a)).right] at h
      rw [
        ←Algebra.groupLCancel R.additive_group
        R.additive_group.id
        (mul R.additive_group.id a)
        (mul R.additive_group.id a)
      ]
      exact h


def isCommutative (_ : Ring X add mul) : Prop :=
  ∀ a b, mul a b = mul b a


def ringHomomorphism (R : Ring X add mul) (S : Ring X' add' mul') (f : α → β) : Prop :=
  (∀ a b, f (add a b) = add' (f a) (f b)) ∧
  (∀ a b, f (mul a b) = mul' (f a) (f b)) ∧
  f R.one = S.one


def homomorphismImage (_ : Ring X add mul) (_ : Ring X' add' mul') (f : α → β) : Set β :=
  { y | ∃ x, x ∈ X ∧ f x = y }


def homomorphismKernel (_ : Ring X add mul) (S : Ring X' add' mul') (f : α → β) : Set α :=
  { x | x ∈ X ∧ f x = S.additive_group.id }


def ideal (R : Ring X add mul) (I : Set α) : Prop :=
  let G := R.additive_group
  G.id ∈ I ∧
  (∀ a b, a ∈ I → b ∈ I → add a b ∈ I) ∧
  (∀ a, a ∈ I → G.inv a ∈ I) ∧
  (∀ r a, r ∈ X → a ∈ I → mul r a ∈ I) ∧
  (∀ r a, r ∈ X → a ∈ I → mul a r ∈ I)


theorem trivialIdeals (R : Ring X add mul) : ideal R {R.additive_group.id} ∧ ideal R X := by
  constructor
  · rw [ideal]
    have h1 := Set.mem_singleton R.additive_group.id
    have h2 :
      ∀ a b, a ∈ ({R.additive_group.id} : Set α) →
      b ∈ ({R.additive_group.id} : Set α) →
      add a b ∈ ({R.additive_group.id} : Set α) := by
        intros a b ha hb
        rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb, (R.additive_group.op_id R.additive_group.id).left]
        exact h1
    have h3 :
      ∀ a, a ∈ ({R.additive_group.id} : Set α) →
      R.additive_group.inv a ∈ ({R.additive_group.id} : Set α) := by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha, Algebra.groupIdInv]
        exact h1
    have h4 :
      ∀ r a, r ∈ X →
      a ∈ ({R.additive_group.id} : Set α) →
      mul r a ∈ ({R.additive_group.id} : Set α) := by
        intros r a hr ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha, (mulId R r).left]
        exact h1
    have h5 :
      ∀ r a, r ∈ X →
      a ∈ ({R.additive_group.id} : Set α) →
      mul a r ∈ ({R.additive_group.id} : Set α) := by
        intros r a hr ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha, (mulId R r).right]
        exact h1
    exact ⟨h1, h2, h3, h4, h5⟩
  · sorry


def unit (R : Ring X add mul) (u : α) : Prop :=
  u ∈ X ∧ ∃ v, v ∈ X ∧ mul u v = R.one ∧ mul v u = R.one


theorem unitUnique (R : Ring X add mul) :
  ∀ u v v',
    (v' ∈ X ∧ mul v' u = R.one ∧ mul u v' = R.one) →
    (v ∈ X ∧ mul u v = R.one ∧ mul v u = R.one) →
    v' = v := by
  intros u v v' hv' hu_inv
  obtain ⟨v'mem, hv'left, hv'right⟩ := hv'
  obtain ⟨hu_invmem, hu_invleft, hu_invright⟩ := hu_inv
  calc
    v' = mul v' (mul u v) := by rw [hu_invleft, (R.mul_id v').right]
    _ = mul (mul v' u) v := by rw [R.mul_assoc]
    _ = mul R.one v := by rw [hv'left]
    _ = v := by rw [(R.mul_id v).left]


structure Field (R : Ring X add mul) (_ : isCommutative R) (_ : R.one ≠ R.additive_group.id) where
  all_units : ∀ x, x ∈ X ∧ x ≠ R.additive_group.id → unit R x


end GaloisTheory
