-- Algebra
--
-- Definitions, Theorems, Exercises

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace Algebra

variable {α : Type} {X : Set α} {op : α → α → α}

structure Group {α : Type} (G : Set α) (op : α → α → α) where
  set : Set α
  id : α
  inv : α → α
  id_mem : id ∈ set
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  op_id : ∀ a, op id a = a ∧ op a id = a
  op_inv : ∀ a, op a (inv a) = id ∧ op (inv a) a = id

structure Ring {α : Type} (R : Set α) (add mul : α → α → α) where
  zero : α
  one : α
  additive_group : Group R add
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_id : ∀ a, mul one a = a ∧ mul a one = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)


lemma groupLMul (_ : Group X op) : ∀ a b c, a = b → op c a = op c b := by
  intro a b c hab
  rw [hab]


lemma groupLCancel (G : Group X op) : ∀ a b c, op c a = op c b → a = b := by
  intro a b c h
  have h' : op (G.inv c) (op c a) = op (G.inv c) (op c b) := by
    rw [h]
  have h'' : op (op (G.inv c) c) a = op (op (G.inv c) c) b := by
    exact G.op_assoc (G.inv c) c a ▸ G.op_assoc (G.inv c) c b ▸ h'
  rw [(G.op_inv c).right] at h''
  rw [(G.op_id a).left, (G.op_id b).left] at h''
  exact h''


def isId (G : Group X op) (e : α) : Prop :=
  e ∈ G.set ∧
  (∀ a, op e a = a) ∧
  (∀ a, op a e = a)


lemma groupUniqueId (G : Group X op) : ∀ e e', isId G e → isId G e' → e = e' := by
  intro e e' he he'
  obtain ⟨hemem, he_left, _⟩ := he
  obtain ⟨he'mem, _, he'_right⟩ := he'
  calc
    e = op e e' := by rw [he'_right e]
    _ = e' := by rw [he_left e']


lemma groupUniqueInv (G : Group X op) : ∀ a b b', op a b = G.id → op a b' = G.id → b = b' := by
  intro a b b' hbinv hb'inv
  have hbinv' : op a b = op a b' := by
    rw [hbinv, hb'inv]
  have hbinv'' : op (G.inv a) (op a b) = op (G.inv a) (op a b') := by
    rw [hbinv']
  have hbinv''' : op (op (G.inv a) a) b = op (op (G.inv a) a) b' := by
    exact G.op_assoc (G.inv a) a b ▸ G.op_assoc (G.inv a) a b' ▸ hbinv''
  rw [(G.op_inv a).right] at hbinv'''
  rw [(G.op_id b).left, (G.op_id b').left] at hbinv'''
  exact hbinv'''


lemma groupInvInv (G : Group X op) : ∀ a, G.inv (G.inv a) = a := by
  intro a
  sorry


def isSubgroup (H G : Group X op) (_ : H.set ⊆ G.set) : Prop :=
  G.id ∈ H.set ∧
  (∀ a b, a ∈ H.set → b ∈ H.set → op a b ∈ H.set) ∧
  (∀ a, a ∈ H.set → G.inv a ∈ H.set)


lemma subgroupEqId (G H : Group X op) (h : H.set ⊆ G.set) : H.id = G.id := by
  apply by_contradiction
  intro hneqid
  have hidHid : isId G H.id := by
    constructor
    · apply Set.mem_of_subset_of_mem h H.id_mem
    · constructor
      · intro a
        exact (H.op_id a).left
      · intro a
        exact (H.op_id a).right
  have hidGid : isId G G.id := by
    constructor
    · exact G.id_mem
    · constructor
      · intro a
        exact (G.op_id a).left
      · intro a
        exact (G.op_id a).right
  have hideq := groupUniqueId G H.id G.id hidHid hidGid
  absurd hideq
  exact hneqid


theorem subgroupTest (H G : Group X op) (h : H.set ⊆ G.set) : isSubgroup H G h ↔
  H.set ≠ ∅ ∧ ∀ a b, a ∈ H.set → b ∈ H.set → op a (G.inv b) ∈ H.set := by
  apply Iff.intro
  · intro hHG -- a b ha hb
    obtain ⟨hid, hclose, hinv⟩ := hHG
    constructor
    · intro hempty
      rw [←Set.not_nonempty_iff_eq_empty] at hempty
      have hnempty := Set.nonempty_of_mem hid
      absurd hnempty
      exact hempty
    · intro a b ha hb
      have hbinv := hinv b hb
      exact hclose a (G.inv b) ha (hbinv)
  · intro hclose
    rw [isSubgroup]
    obtain ⟨hnempty, hclose⟩ := hclose
    constructor
    · rw [← subgroupEqId G H h]
      exact H.id_mem
    · constructor
      · intro a b ha hb
        sorry
      · sorry


def groupIntegers : Group (Set.univ : Set ℤ) (fun a b => a + b) where
  set := Set.univ
  id := 0
  inv := fun a => -a
  id_mem := by
    exact Set.mem_univ 0
  op_assoc := by
    exact Int.add_assoc
  op_id := by
    intro a
    exact ⟨Int.zero_add a, Int.add_zero a⟩
  op_inv := by
    intro a
    exact ⟨Int.add_right_neg a, Int.add_left_neg a⟩

def groupPrimeIntegers (p : ℕ) (h : Nat.Prime p) :
  Group (Set.univ : Set (Fin p)) (
    fun a b => ⟨(a.val + b.val) % p, by
      apply Nat.mod_lt
      exact Nat.Prime.pos h⟩
    ) where
  set := Set.univ
  id := ⟨0, by exact Nat.Prime.pos h⟩
  inv := fun a => ⟨(p - a.val) % p, by
    apply Nat.mod_lt
    exact Nat.Prime.pos h⟩
  id_mem := by
    exact Set.mem_univ (⟨0, by exact Nat.Prime.pos h⟩ : Fin p)
  op_assoc := by
    intro a b c
    simp
    ring_nf
  op_id := by
    intro a
    simp only [zero_add, add_zero, and_self]
    apply Fin.ext
    simp [Nat.mod_eq_of_lt a.isLt]
  op_inv := by
    intro a
    simp

end Algebra
