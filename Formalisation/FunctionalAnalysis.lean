-- Functional Analysis - 2025/26
--
-- Definitions, Theorems, Exercises

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Algebra.Group.Defs


namespace FunctionalAnalysis

variable {α β : Type} {X : Set α} {K : Field β}
variable [Add α] [SMul β α] [Neg α]

structure VectorSpace (X : Set α) (K : Field β) [Add α] [SMul β α] [Neg α] where
    zero : α
    add_comm : ∀ u v : α, u + v = v + u
    add_assoc : ∀ u v w : α, (u + v) + w = u + (v + w)
    add_zero : ∀ v, v + zero = v
    add_neg : ∀ v, v + -v = zero
    smul_assoc : ∀ a b : β, ∀ v : α, a • (b • v) = (a * b) • v
    smul_one : ∀ v : α, (1 : β) • v = v
    add_distrib : ∀ a : β, ∀ u v : α, a • (u + v) = (a • u) + (a • v)
    smul_distrib : ∀ a b : β, ∀ v : α, (a + b) • v = (a • v) + (b • v)


structure RVectorSpace (X : Set α) [Add α] [SMul ℝ α]
  extends VectorSpace X (inferInstance : Field ℝ)


lemma vspace_add_equiv (V : VectorSpace X K) : ∀ u v w : α, u = v ↔ w + u = w + v := by
  intro u v w
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    have h1 : -w + (w + v) = -w + (w + u) := by
      rw [h]
    rw [← V.add_assoc, ← V.add_assoc] at h1
    nth_rewrite 2 [V.add_comm] at h1
    nth_rewrite 4 [V.add_comm] at h1
    rw [V.add_neg, V.add_comm, V.add_zero, V.add_comm, V.add_zero] at h1
    symm
    exact h1


lemma vspace_neg_unique (V : VectorSpace X K) :
  ∀ v w, v + w = V.zero → w = -v := by
  intro v w h
  have := V.add_neg v
  rw [← h] at this
  symm
  apply (vspace_add_equiv V (-v) w v).mpr
  exact this


structure NormedSpace (X : Set α) [Add α] [SMul ℝ α]
  extends RVectorSpace X where
    norm : α → ℝ
    norm_nonneg : ∀ x, norm x ≥ 0
    norm_zero : ∀ x, norm x = 0 ↔ x = zero
    norm_scalar_mul : ∀ x a, norm (a • x) = abs a * norm x
    norm_triangle : ∀ x y, norm (x + y) ≤ norm x + norm y


def induced_metric [Add α] [SMul ℝ α] (V : NormedSpace X) : α → α → ℝ :=
  fun x y => V.norm (x + -y)


structure MetricSpace (X : Set α) (d : α → α → ℝ) where
  metric_nonneg : ∀ x y, d x y ≥ 0
  metric_zero : ∀ x y, d x y = 0 ↔ x = y
  metric_symm : ∀ x y, d x y = d y x
  metric_triangle : ∀ x y z, d x z ≤ d x y + d y z


-- Exercise Sheet 1
-- 1.
theorem smul_zero (V : VectorSpace X K) : ∀ u : α, (0 : β) • u = V.zero := by
  let z : β := 0
  intro u
  have h : z • u = z • u + z • u := by
    rw [← V.smul_distrib]
    rw [zero_add]
  have hcancel := V.add_neg (z • u)
  have h' := (vspace_add_equiv V
    (z • u) ((z • u) + (z • u)) (-(z • u))).mp h
  rw [V.add_comm, hcancel, ←V.add_assoc] at h'
  nth_rewrite 1 [V.add_comm] at h'
  nth_rewrite 2 [V.add_comm] at h'
  rw [hcancel, V.add_zero] at h'
  symm
  exact h'

theorem smul_zero_left (V : VectorSpace X K) : ∀ a : β, a • V.zero = V.zero := by
  intro a
  have h : a • V.zero = a • V.zero + a • V.zero := by
    rw [← V.add_distrib]
    rw [V.add_zero]
  have cancel := V.add_neg (a • V.zero)
  have h' := (vspace_add_equiv V
    (a • V.zero) ((a • V.zero) + (a • V.zero)) (-(a • V.zero))).mp h
  rw [V.add_comm, cancel, ←V.add_assoc] at h'
  nth_rewrite 1 [V.add_comm] at h'
  nth_rewrite 2 [V.add_comm] at h'
  rw [cancel, V.add_zero] at h'
  symm
  exact h'

theorem smul_neg_one (V : VectorSpace X K) : ∀ u : α, (-1 : β) • u = -u := by
  let one : β := 1
  let neg_one : β := -1
  intro u
  have h := (vspace_add_equiv V (one • u) u (neg_one • u)).mp (V.smul_one u)
  rw [← V.smul_distrib, K.neg_add_cancel, smul_zero V] at h
  apply vspace_neg_unique V u ((-1) • u)
  rw [h, V.add_comm]


-- 2.
section FunctionVSpace

local instance : Add (α → β) := ⟨fun f g x => f x + g x⟩
local instance : SMul β (α → β) := ⟨fun a f x => a * f x⟩
local instance : Neg (α → β) := ⟨fun f x => -(f x)⟩

def k_functions_vspace (K : Field β) :
    VectorSpace (Set.univ : Set (α → β)) K where
  zero         := fun _ => 0
  add_comm     := by intros; ext; simp only [Pi.add_apply, K.add_comm]
  add_assoc    := by intros; ext; simp only [Pi.add_apply, K.add_assoc]
  add_zero     := by intros; ext; simp
  add_neg      := by intros; ext; simp
  smul_assoc   := by intros; ext; simp only [Pi.smul_apply, smul_eq_mul]; rw [K.mul_assoc]
  smul_one     := by simp;
  add_distrib  := by
    intro a f g
    ext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [K.left_distrib]
  smul_distrib := by
    intros
    ext
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [K.right_distrib]

end FunctionVSpace


--


lemma vspace_add_pm (V : VectorSpace X K) : ∀ u v : α, u = (u + v) + (-v) := by
  intro u v
  rw [V.add_assoc, V.add_neg, V.add_zero]


theorem norm_is_metric [Add α] [SMul ℝ α] [Neg α] (V : NormedSpace X) :
  MetricSpace X (induced_metric V) where
    metric_nonneg := by
      intro x y
      exact V.norm_nonneg (x + -y)
    metric_zero := by
      intro x y
      rw [induced_metric, V.norm_zero]
      apply Iff.intro
      · intro h
        rw [vspace_add_equiv V.toVectorSpace (x + -y) V.zero y] at h
        rw [V.add_comm, V.add_assoc] at h
        nth_rewrite 2 [V.add_comm] at h
        rw [V.add_neg, V.add_zero, V.add_zero] at h
        exact h
      · intro h
        rw [h, V.add_neg]
    metric_symm := by
      intro x y
      rw [induced_metric, induced_metric]
      nth_rewrite 1 [← smul_neg_one V.toVectorSpace y, V.add_comm]
      sorry
    metric_triangle := by
      intro x y z
      rw [induced_metric, induced_metric, induced_metric]
      nth_rewrite 1 [vspace_add_pm V.toVectorSpace (-z) y]
      rw [V.add_assoc (-z) y (-y), V.add_comm y (-y)]
      rw [← V.add_assoc (-z) (-y) y, V.add_comm (-z) (-y)]
      rw [V.add_assoc (-y) (-z) y, V.add_comm (-z) y, ← V.add_assoc]
      exact V.norm_triangle (x + -y) (y + -z)


-- Exercise Sheet 2
-- 1.
lemma neg_norm_eq [SMul ℝ α] (V : NormedSpace X) :
  ∀ x, V.norm (-x) = V.norm x := by
    intro x
    have h := V.norm_scalar_mul x (-1)
    rw [smul_neg_one V.toVectorSpace] at h
    rw [abs_neg, abs_of_pos, one_mul] at h
    · exact h
    · simp

theorem reverse_triangle_inequality [SMul ℝ α] (V : NormedSpace X) :
  ∀ x y, abs (V.norm x - V.norm y) ≤ V.norm (x + -y) := by
    intro x y
    have h := V.norm_triangle (x + -y) (y)
    rw [V.add_assoc, V.add_comm (-y) y, V.add_neg, V.add_zero] at h
    have h' := add_le_add_right h (- V.norm y)
    nth_rewrite 1 [add_comm] at h'
    nth_rewrite 2 [add_comm] at h'
    rw [add_assoc, add_neg_cancel, add_zero, ← sub_eq_add_neg] at h'
    rw [abs_sub_le_iff]
    constructor
    · exact h'
    · have h_sym := V.norm_triangle y (-x)
      have hn := neg_norm_eq V x
      sorry


--


lemma neg_distrib_add (V : VectorSpace X K)
  : ∀ u v : α, -(u + v) = (-u) + (-v) := by
    intro u v
    rw [← smul_neg_one V (u + v), V.add_distrib, smul_neg_one V u, smul_neg_one V v]


lemma translation_invariance_1 [SMul ℝ α] (V : NormedSpace X) :
  ∀ x y a : α, induced_metric V (x + a) (y + a) = induced_metric V x y := by
    intro x y a
    rw [induced_metric, induced_metric]
    rw [neg_distrib_add V.toVectorSpace]
    rw [
      V.add_assoc, V.add_comm (-y) (-a),
      ← V.add_assoc a, V.add_neg, V.add_comm V.zero, V.add_zero
    ]


lemma neg_distrib_smul (V : VectorSpace X K)
  : ∀ a: β, ∀ v : α, -(a • v) = a • (-v) := by
    intro a v
    rw [← smul_neg_one V (a • v), V.smul_assoc, mul_comm, ← V.smul_assoc, smul_neg_one V]


lemma translation_invariance_2 [SMul ℝ α] (V : NormedSpace X) :
  ∀ x y a, induced_metric V (a • x) (a • y) = abs a * induced_metric V x y := by
    intro x y a
    rw [induced_metric, induced_metric]
    rw [neg_distrib_smul V.toVectorSpace, ← V.add_distrib, V.norm_scalar_mul]


end FunctionalAnalysis
