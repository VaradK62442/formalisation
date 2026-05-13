-- Functional Analysis - 2025/26
--
-- Definitions, Theorems, Exercises

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NthRewrite


namespace FunctionalAnalysis

variable {α β : Type} {X : Set α} {K : Field β}
variable {add : α → α → α} {smul : β → α → α}
variable {rsmul : ℝ → α → α}

structure VectorSpace (X : Set α) (K : Field β)
  (add : α → α → α) (smul : β → α → α) where
    zero : α
    neg : α → α
    add_comm : ∀ u v, add u v = add v u
    add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
    add_zero : ∀ v, add v zero = v
    add_neg : ∀ v, add v (neg v) = zero
    smul_assoc : ∀ a b v, smul a (smul b v) = smul (a * b) v
    smul_one : ∀ v, smul 1 v = v
    add_distrib : ∀ a u v, smul a (add u v) = add (smul a u) (smul a v)
    smul_distrib : ∀ a b v, smul (a + b) v = add (smul a v) (smul b v)


structure RVectorSpace (X : Set α)
  (add : α → α → α) (smul : ℝ → α → α)
  extends VectorSpace X (inferInstance : Field ℝ) add smul


lemma vspace_add_equiv (V : VectorSpace X K add smul) : ∀ u v w, u = v ↔ add w u = add w v := by
  intro u v w
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    have h1 : add (V.neg w) (add w v) = add (V.neg w) (add w u) := by
      rw [h]
    rw [← V.add_assoc, ← V.add_assoc] at h1
    nth_rewrite 2 [V.add_comm] at h1
    nth_rewrite 4 [V.add_comm] at h1
    rw [V.add_neg, V.add_comm, V.add_zero, V.add_comm, V.add_zero] at h1
    symm
    exact h1


lemma vspace_neg_unique (V : VectorSpace X K add smul) :
  ∀ v w, add v w = V.zero → w = V.neg v := by
  intro v w h
  have := V.add_neg v
  rw [← h] at this
  symm
  apply (vspace_add_equiv V (V.neg v) w v).mpr
  exact this


structure NormedSpace (X : Set α)
  (add : α → α → α) (rsmul : ℝ → α → α)
  extends RVectorSpace X add rsmul where
    norm : α → ℝ
    norm_nonneg : ∀ x, norm x ≥ 0
    norm_zero : ∀ x, norm x = 0 ↔ x = zero
    norm_scalar_mul : ∀ x a, norm (rsmul a x) = abs a * norm x
    norm_triangle : ∀ x y, norm (add x y) ≤ norm x + norm y


def metric_on_norm (V : NormedSpace X add rsmul) : α → α → ℝ :=
  fun x y => V.norm (add x (V.neg y))


-- Exercise Sheet 1
-- 1.
theorem smul_zero (V : VectorSpace X K add smul) : ∀ u, smul 0 u = V.zero := by
  intro u
  have h : smul 0 u = add (smul 0 u) (smul 0 u) := by
    rw [← V.smul_distrib]
    rw [zero_add]
  have cancel := V.add_neg (smul 0 u)
  have h' := (vspace_add_equiv V (smul 0 u) (add (smul 0 u) (smul 0 u)) (V.neg (smul 0 u))).mp h
  rw [V.add_comm, cancel, ←V.add_assoc] at h'
  nth_rewrite 1 [V.add_comm] at h'
  nth_rewrite 2 [V.add_comm] at h'
  rw [cancel, V.add_zero] at h'
  symm
  exact h'

theorem smul_zero_left (V : VectorSpace X K add smul) : ∀ a, smul a V.zero = V.zero := by
  intro a
  have h : smul a V.zero = add (smul a V.zero) (smul a V.zero) := by
    rw [← V.add_distrib]
    rw [V.add_zero]
  have cancel := V.add_neg (smul a V.zero)
  have h' := (vspace_add_equiv V
    (smul a V.zero) (add (smul a V.zero) (smul a V.zero)) (V.neg (smul a V.zero))).mp h
  rw [V.add_comm, cancel, ←V.add_assoc] at h'
  nth_rewrite 1 [V.add_comm] at h'
  nth_rewrite 2 [V.add_comm] at h'
  rw [cancel, V.add_zero] at h'
  symm
  exact h'

theorem smul_neg_one (V : VectorSpace X K add smul) : ∀ u, smul (-1) u = V.neg u := by
  intro u
  have h := (vspace_add_equiv V (smul 1 u) u (smul (-1) u)).mp (V.smul_one u)
  rw [← V.smul_distrib, K.neg_add_cancel, smul_zero V] at h
  apply vspace_neg_unique V u (smul (-1) u)
  rw [h, V.add_comm]


-- 2.
def k_functions_vspace (K : Field β) :
  VectorSpace (Set.univ : Set (α → β)) K
  (fun f g => fun x => f x + g x)
  (fun a f => fun x => a * f x) where
  zero := fun x => 0
  neg := fun f => fun x => - (f x)
  add_comm := by
    intro f g
    ext x
    rw [K.add_comm]
  add_assoc := by
    intro f g h
    ext x
    rw [K.add_assoc]
  add_zero := by
    intro f
    ext x
    rw [K.add_zero]
  add_neg := by
    simp
  smul_assoc := by
    intro a b h
    ext x
    rw [K.mul_assoc]
  smul_one := by
    simp
  add_distrib := by
    intros
    ext
    rw [K.left_distrib]
  smul_distrib := by
    intros
    ext
    rw [K.right_distrib]


-- Exercise Sheet 2
-- 1.
lemma neg_norm_eq (V : NormedSpace X add rsmul) : ∀ x, V.norm (V.neg x) = V.norm x := by
  intro x
  have h := V.norm_scalar_mul x (-1)
  rw [smul_neg_one V.toVectorSpace] at h
  rw [abs_neg, abs_of_pos, one_mul] at h
  · exact h
  · simp

theorem reverse_triangle_inequality (V : NormedSpace X add rsmul) :
  ∀ x y, abs (V.norm x - V.norm y) ≤ V.norm (add x (V.neg y)) := by
  intro x y
  have h := V.norm_triangle (add x (V.neg y)) (y)
  rw [V.add_assoc, V.add_comm (V.neg y) y, V.add_neg, V.add_zero] at h
  have h' := add_le_add_right h (- V.norm y)
  nth_rewrite 1 [add_comm] at h'
  nth_rewrite 2 [add_comm] at h'
  rw [add_assoc, add_neg_cancel, add_zero, ← sub_eq_add_neg] at h'
  rw [abs_sub_le_iff]
  constructor
  · exact h'
  · have h_sym := V.norm_triangle y (V.neg x)
    have hn := neg_norm_eq V x
    sorry

end FunctionalAnalysis
