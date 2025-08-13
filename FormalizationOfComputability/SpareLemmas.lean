/- Lemmata that are correct, but aren't needed anywhere (yet?) -/

import FormalizationOfComputability.PhiSeq
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Set.Lattice

lemma List.count_pos_of_mem {α : Type*} [DecidableEq α] {a : α} {L : List α}
    (h : a ∈ L) : 0 < List.count a L := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.count, List.mem_cons] at *
    cases h <;> simp_all

/- A lemma for splitting up a union over the naturals.
Probably something close is in Mathlib already!-/
lemma Union_split (t : ℕ) (p : ℕ → Set ℕ) :
    ⋃ s, p s = (⋃ (s<t), p s) ∪ (⋃ (s ≥ t), p s) := by
  apply subset_antisymm
  · intro x h3
    simp at h3
    obtain ⟨i, h3⟩ := h3
    by_cases h4 : i < t
    · left
      exact Set.mem_biUnion h4 h3
    · right
      simp at h4
      exact Set.mem_biUnion h4 h3
  · simp
    constructor
    · intro i h3
      exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
    · intro i h3
      exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a

open Computability

/- ϕ_e(n) halts iff n appears in some WPrefix as the kth element -/
lemma kth_mem (e n : ℕ) : (Phi_halts e n) ↔
    ∃ s, (∃ k, k.isSome ∧ k = (WPrefix e s).idxOf? n) := by
  constructor
  · rw [phi_halts_runtime_exists]
    intro h
    obtain ⟨r, h⟩ := h
    use r
    rw [← PhiNew_runtime] at h
    have h1 : n ∈ W_s e r := by
      rw [Ws_eq]
      exact Finset.mem_union_right (W_s e (r - 1)) h
    rw [← WPrefix_mem] at h1
    let m := (WPrefix e r).idxOf? n
    use m
    constructor
    · exact List.isSome_idxOf?.mpr h1
    · rfl
  · intro ⟨s, ⟨k, ⟨h, h1⟩⟩⟩
    simp [h1] at h
    rw [← WPrefix_phi]
    use s

/- If A is a suffix of B, then A++C is a suffix of B++C -/
lemma List.isSuffix_append {α : Type} (A B C : List α) (h : A <:+ B) :
    A ++ C <:+ B ++ C := by
  obtain ⟨T, h⟩ := h
  use T
  rw [← append_assoc, h]

#min_imports
