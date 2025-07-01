/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find

/- These lemmas need to find their way into the List API. -/
open List
open Nat

theorem idxOf?_mem {α : Type} [inst : DecidableEq α] {a : α} {n : ℕ} {L : List α}
    (h : n = List.idxOf? a L) : L[n]? = a := by
  have := List.of_findIdx?_eq_some h.symm
  generalize hi : L[n]? = i at this ⊢
  cases i <;> simp_all

/- this can be strengthened to iff h -/
theorem mem_idxOf_iff {α : Type} [inst : DecidableEq α] {a : α} {n : ℕ} {L : List α}
    (h : ∀ i < n, L[i]? ≠ a) : n = List.idxOf? a L ↔ L[n]? = a := by
  constructor
  · exact fun a_1 ↦ idxOf?_mem a_1
  · intro h1
    have h2 : n < L.length := by
      exact (isSome_getElem? L n).mp (Option.isSome_of_mem h1)
    have h3 : L[n] = a := by
      exact (List.getElem_eq_iff h2).mpr h1
    rw [List.idxOf?, eq_comm, List.findIdx?_eq_some_iff_findIdx_eq, List.findIdx_eq]
    constructor
    · exact h2
    · constructor
      · simp [h2, h3]
      · intro j hjn
        simp
        apply h at hjn
        push_neg
        by_contra h5
        rw [← h5] at hjn
        revert hjn
        simp
    · exact h2

theorem index_head {α : Type} {a : α} {L : List α} :
    some a = L.head? ↔ L[0]? = a := by
  unfold List.head?
  cases L <;> simp_all
  exact eq_comm

theorem index_tail {α : Type} [inst : DecidableEq α] {a : α} {L : List α} :
    a ∈ L.tail ↔ ∃ n ≥ 1, L[n]? = a := by
  cases' L with b T
  · simp
  · simp
    constructor
    · intro h
      rw [← List.isSome_idxOf?] at h
      have h1 : ∃ n, some n = idxOf? a T := by
        refine Option.ne_none_iff_exists.mp ?_
        exact Option.isSome_iff_ne_none.mp h
      obtain ⟨n, h1⟩ := h1
      apply idxOf?_mem at h1
      use n+1
      constructor
      · exact Nat.le_add_left 1 n
      · simp [h1]
    · intro ⟨n, ⟨h, h1⟩⟩
      apply Nat.exists_eq_add_of_le at h
      obtain ⟨k, h⟩ := h
      rw [h, add_comm] at h1
      simp at h1
      exact mem_of_getElem? h1

theorem index_tail_minus_one {α : Type} [inst : DecidableEq α] {a : α} {L : List α}
    (h : a ∈ L.tail) : a = L.head? ∨ idxOf? a L.tail = (List.idxOf? a L).map (· - 1) := by
  cases' L with b T
  · tauto
  · by_cases h1 : a = (b :: T).head?
    · left
      exact h1
    · right
      rw [index_tail] at h
      let k := Nat.find h
      have ⟨hk1, hk2⟩ := Nat.find_spec h
      apply Nat.exists_eq_add_of_le at hk1
      obtain ⟨l, h2⟩ := hk1
      simp at h1
      rw [add_comm] at h2
      simp
      have h3 : ∀ i < k, (b :: T)[i]? ≠ a := by
        intro i hik
        apply Nat.find_min h at hik
        simp at hik
        by_cases hi : i=0
        · simp [hi, eq_comm, h1]
        · exact hik (one_le_iff_ne_zero.mpr hi)
      have h4 : ∀ i < l, T[i]? ≠ a := by
        intro i hik
        by_cases hi : i + 1 < k
        · apply h3 at hi
          simp at hi
          exact hi
        · unfold k at hi
          simp [h2] at hi
          contrapose hik
          exact Nat.not_lt.mpr hi
      apply mem_idxOf_iff at h3
      apply mem_idxOf_iff at h4
      simp [k, Nat.find_spec h] at h3
      rw [← h3]
      simp
      rw [eq_comm] at h4
      simp_all [h4, h, h2]

theorem List.idxOf?_append {α : Type} [BEq α] [LawfulBEq α] {l₁ l₂ : List α} {a : α} :
    idxOf? a (l₁ ++ l₂) = if a ∈ l₁ then idxOf? a l₁
    else (List.idxOf? a l₂).map (· + l₁.length) := by
    split <;> (rename_i h)
    <;> unfold idxOf?
    <;> rw [List.findIdx?_append]
    · refine Option.or_of_isSome ?_
      simp [h]
    · refine Option.or_of_isNone ?_
      simp
      exact fun x a_1 ↦ ne_of_mem_of_not_mem a_1 h

lemma idxOf?_length {α : Type} [inst : DecidableEq α] {a : α} {n : ℕ} {L : List α}
    (h : some n = idxOf? a L) : n < L.length := by
  have h1 : L[n]?.isSome = true := by
    apply Option.isSome_of_mem
    apply idxOf?_mem
    exact h
  exact isSome_getElem?.mp h1
