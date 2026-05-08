-- Algebra
--
-- Definitions, Theorems, Exercises

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace Algebra

variable {α : Type} {X Y : Set α} {op op' : α → α → α}

structure Group (G : Set α) (op : α → α → α) where
  id : α
  inv : α → α
  id_mem : id ∈ G
  op_closed : ∀ a b, a ∈ G → b ∈ G → op a b ∈ G
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  op_id : ∀ a, op id a = a ∧ op a id = a
  op_inv_exists : ∀ a, ∃ b, b ∈ G ∧ op a b = id ∧ op b a = id
  inv_is_inv : ∀ a, op a (inv a) = id ∧ op (inv a) a = id


def isId (_ : Group X op) (e : α) : Prop :=
  e ∈ X ∧
  (∀ a, op e a = a) ∧
  (∀ a, op a e = a)


def isInv (G : Group X op) (a b : α) : Prop :=
  op a b = G.id ∧
  op b a = G.id


lemma groupLMul (_ : Group X op) : ∀ a b c, a = b → op c a = op c b := by
  intro a b c hab
  rw [hab]


lemma groupRMul (_ : Group X op) : ∀ a b c, a = b → op a c = op b c := by
  intro a b c hab
  rw [hab]


lemma groupLCancel (G : Group X op) : ∀ a b c, op c a = op c b → a = b := by
  intro a b c h
  apply Exists.elim (G.op_inv_exists c)
  intro c' hc'
  have h' : op c' (op c a) = op c' (op c b) := by
    rw [h]
  have h'' : op (op c' c) a = op (op c' c) b := by
    exact G.op_assoc c' c a ▸ G.op_assoc c' c b ▸ h'
  rw [hc'.right.right] at h''
  rw [(G.op_id a).left, (G.op_id b).left] at h''
  exact h''


lemma groupUniqueId (G : Group X op) : ∀ e e', isId G e → isId G e' → e = e' := by
  intro e e' he he'
  obtain ⟨hemem, he_left, _⟩ := he
  obtain ⟨he'mem, _, he'_right⟩ := he'
  calc
    e = op e e' := by rw [he'_right e]
    _ = e' := by rw [he_left e']


lemma groupSideInv (G : Group X op) : ∀ a b, op a b = G.id → op b a = G.id := by
  intro a b hab
  apply Exists.elim (G.op_inv_exists a)
  intro a' ha'
  have h : op a' (op a b) = op a' G.id := by
    rw [hab]
  have h' : op (op a' a) b = a' := by
    rw [G.op_assoc a' a b]
    rw [(G.op_id a').right] at h
    exact h
  apply groupRMul G (op (op a' a) b) a' (G.inv b) at h'
  rw [G.op_assoc a' a b, G.op_assoc, G.op_assoc, (G.inv_is_inv b).left, (G.op_id a).right] at h'
  apply groupLCancel G a (G.inv b) a' at h'
  rw [h']
  rw [(G.inv_is_inv b).left]


lemma groupUniqueInv (G : Group X op) : ∀ a b b', isInv G a b → isInv G a b' → b = b' := by
  intro a b b' hbinv hb'inv
  rw [isInv] at hbinv hb'inv
  obtain ⟨hbinv, _⟩ := hbinv
  obtain ⟨hb'inv, _⟩ := hb'inv
  rw [←hbinv] at hb'inv
  apply groupLCancel G b' b a at hb'inv
  symm
  exact hb'inv


lemma groupInvInv (G : Group X op) : ∀ a, G.inv (G.inv a) = a := by
  intro a
  apply Exists.elim (G.op_inv_exists a)
  intro a' ⟨_, h, h'⟩
  have h'' : a' = G.inv a := by
    apply groupUniqueInv G a a' (G.inv a) ⟨h, h'⟩ (G.inv_is_inv a)
  rw [←h'']
  apply groupUniqueInv G a' (G.inv a') a (G.inv_is_inv a') ⟨h', h⟩


lemma groupIdInv (G : Group X op) : G.inv G.id = G.id := by
  apply groupUniqueInv G G.id (G.inv G.id) G.id (G.inv_is_inv G.id)
  rw [isInv]
  exact G.op_id G.id


def isSubgroup (_ : Group Y op) (G : Group X op) (_ : Y ⊆ X) : Prop :=
  G.id ∈ Y ∧
  (∀ a b, a ∈ Y → b ∈ Y → op a b ∈ Y) ∧
  (∀ a, a ∈ Y → G.inv a ∈ Y)


lemma subsetEqId (G : Group X op) (H : Group Y op) (h : Y ⊆ X) : H.id = G.id := by
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


theorem subgroupTest (H : Group Y op) (G : Group X op) (h : Y ⊆ X) : isSubgroup H G h ↔
  Y ≠ ∅ ∧ ∀ a b, a ∈ Y → b ∈ Y → op a (G.inv b) ∈ Y := by
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
    · rw [← subsetEqId G H h]
      exact H.id_mem
    · constructor
      · intro a b ha hb
        have h' : G.id ∈ Y := by
          rw [← subsetEqId G H h]
          exact H.id_mem
        have hbinv : (G.inv b) ∈ Y := by
          have hidop := hclose G.id b h' hb
          rw [(G.op_id (G.inv b)).left] at hidop
          exact hidop
        have h'' : op a (G.inv (G.inv b)) ∈ Y := by
          apply hclose a (G.inv b) ha hbinv
        rw [groupInvInv G b] at h''
        exact h''
      · intro a ha
        have h' : G.id ∈ Y := by
          rw [← subsetEqId G H h]
          exact H.id_mem
        have hidop := hclose G.id a h' ha
        rw [(G.op_id (G.inv a)).left] at hidop
        exact hidop


def isAbelian (_ : Group X op) : Prop :=
  ∀ a b, op a b = op b a


def groupIntegers : Group (Set.univ : Set ℤ) (fun a b => a + b) where
  id := 0
  inv := fun a => -a
  id_mem := by
    exact Set.mem_univ 0
  op_closed := by
    intros a b ha hb
    exact Set.mem_univ (a + b)
  op_assoc := by
    exact Int.add_assoc
  op_id := by
    intro a
    exact ⟨Int.zero_add a, Int.add_zero a⟩
  op_inv_exists := by
    intro a
    apply Exists.intro (-a)
    exact ⟨Set.mem_univ (-a), Int.add_right_neg a, Int.add_left_neg a⟩
  inv_is_inv := by
    simp

def groupPrimeIntegers (p : ℕ) (h : Nat.Prime p) :
  Group (Set.univ : Set (Fin p)) (
    fun a b => ⟨(a.val + b.val) % p, by
      apply Nat.mod_lt
      exact Nat.Prime.pos h⟩
    ) where
  id := ⟨0, by exact Nat.Prime.pos h⟩
  inv := fun a => ⟨(p - a.val) % p, by
    apply Nat.mod_lt
    exact Nat.Prime.pos h⟩
  id_mem := by
    exact Set.mem_univ (⟨0, by exact Nat.Prime.pos h⟩ : Fin p)
  op_closed := by
    intros a b ha hb
    exact Set.mem_univ _
  op_assoc := by
    intro a b c
    simp
    ring_nf
  op_id := by
    intro a
    simp only [zero_add, add_zero, and_self]
    apply Fin.ext
    simp [Nat.mod_eq_of_lt a.isLt]
  op_inv_exists := by
    intro a
    use ⟨(p - a.val) % p, by
      apply Nat.mod_lt
      exact Nat.Prime.pos h⟩
    simp
  inv_is_inv := by
    simp

end Algebra
