-- Algebraic and Geometric Topology - 2025/26
--
-- Definitions, Theorems, Homework exercises
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

namespace AGT

variable {α : Type} {X : Set α}

structure Topology X where
  openSets : Set (Set X)
  univ_open : Set.univ ∈ openSets
  empty_open : ∅ ∈ openSets
  inter_open : ∀ U ∈ openSets, ∀ V ∈ openSets, U ∩ V ∈ openSets
  union_open : ∀ F ⊆ openSets, ⋃₀ F ∈ openSets


def indiscreteTopology X : Topology X where
  openSets := {∅, Set.univ}
  univ_open := by
    right
    rfl
  empty_open := by
    left
    rfl
  inter_open := by
    intro U hU V hV
    cases hU with
    | inl hUempty =>
      rw [hUempty]
      rw [Set.empty_inter]
      left
      rfl
    | inr hUuniv =>
      rw [hUuniv]
      rw [Set.univ_inter]
      exact hV
  union_open := by
    sorry


def isBasis (B : Set (Set α)) (T : Topology X) : Prop :=
  ∀ U ∈ T.openSets, ∃ V ⊆ B, ⋃₀ V = U

-- HW1

-- 1.1 a)
example (B : Set (Set α)) (T : Topology X) :
  isBasis B T ↔ ∀ U ∈ T.openSets, ∀ p ∈ U, ∃ b ∈ B, p ∈ b ∧ b ⊆ U := by
  apply Iff.intro
  · intro hB U hUopen p hpU
    obtain ⟨V, hVsubB, hVunionU⟩ := hB U hUopen
    rw [← hVunionU] at hpU
    obtain ⟨b, hbV, hpb⟩ := hpU
    refine ⟨b, hVsubB hbV, hpb, ?_⟩
    intro x hx
    rw [← hVunionU]
    exact ⟨b, hbV, hx⟩
  · intro hB U hUopen
    cases (Classical.em (U = ∅)) with
    | inl hUempty =>
      rw [hUempty]
      use ∅
      simp only [Set.empty_subset, true_and]
      ext x
      simp
    | inr hUnonempty =>
      use {b ∈ B | b ⊆ U}
      constructor
      · intro U_p hU_p
        exact hU_p.left
      · ext x
        constructor
        · intro hx
          obtain ⟨b, ⟨_, hbU⟩, hxb⟩ := hx
          exact hbU hxb
        · intro hx
          obtain ⟨b, hbB, hxb, hbU⟩ := hB U hUopen x hx
          exact ⟨b, ⟨hbB, hbU⟩, hxb⟩


end AGT
