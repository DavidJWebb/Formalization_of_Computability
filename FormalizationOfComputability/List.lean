/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Data.List.Basic



/- These lemmas need to find their way into the List API. -/
open List
open Nat

variable {α} [inst : DecidableEq α] {a b x : α} {n : ℕ} {L : List α}

theorem idxOf?_getElem? (h : n = List.idxOf? a L) : L[n]? = a := by
  have := List.of_findIdx?_eq_some h.symm
  generalize hi : L[n]? = i at this ⊢
  cases i <;> simp_all

/- this can be strengthened to iff h -/
theorem idxOf?_getElem?_iff (h : ∀ i < n, L[i]? ≠ a) : n = List.idxOf? a L ↔ L[n]? = a := by
  constructor
  · exact fun a_1 ↦ idxOf?_getElem? a_1
  · intro h1
    have h2 : n < L.length := (isSome_getElem? L n).mp (Option.isSome_of_mem h1)
    have h3 : L[n] = a := (List.getElem_eq_iff h2).mpr h1
    rw [List.idxOf?, eq_comm, List.findIdx?_eq_some_iff_findIdx_eq, List.findIdx_eq]
    constructor
    · exact h2
    · constructor
      · simp [h3]
      · intro j hjn
        simp only [beq_eq_false_iff_ne, ne_eq]
        apply h at hjn
        push_neg
        by_contra h5
        rw [← h5] at hjn
        revert hjn
        simp
    · exact h2

/- This allows for some theorems to have easier to state hypotheses -/
theorem idxOf?_mem (h : n = List.idxOf? a L) : a ∈ L :=
  isSome_idxOf?.mp (Option.isSome_of_mem (id (Eq.symm h)))

theorem index_head {α} {a : α} {L : List α} : some a = L.head? ↔ L[0]? = a := by
  unfold List.head?
  cases L <;> simp_all
  exact eq_comm

theorem index_tail : a ∈ L.tail ↔ ∃ n ≥ 1, L[n]? = a := by
  cases L with | nil | cons b T
  · simp
  · simp only [tail_cons, ge_iff_le]
    constructor
    · intro h
      rw [← List.isSome_idxOf?] at h
      have h1 := Option.ne_none_iff_exists.mp (Option.isSome_iff_ne_none.mp h)
      obtain ⟨n, h1⟩ := h1
      apply idxOf?_getElem? at h1
      use n+1
      constructor
      · exact Nat.le_add_left 1 n
      · simp [h1]
    · intro ⟨n, ⟨h, h1⟩⟩
      apply Nat.exists_eq_add_of_le at h
      obtain ⟨k, h⟩ := h
      rw [h, add_comm] at h1
      simp only [getElem?_cons_succ] at h1
      exact mem_of_getElem? h1

theorem index_tail_minus_one (h : a ∈ L.tail) :
    a = L.head? ∨ idxOf? a L.tail = (List.idxOf? a L).map (· - 1) := by
  cases L with | nil | cons b T
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
      simp only [head?_cons, Option.some.injEq] at h1
      rw [add_comm] at h2
      simp only [tail_cons]
      have h3 : ∀ i < k, (b :: T)[i]? ≠ a := by
        intro i hik
        apply Nat.find_min h at hik
        simp only [ge_iff_le, not_and] at hik
        by_cases hi : i=0
        · simp [hi, eq_comm, h1]
        · exact hik (one_le_iff_ne_zero.mpr hi)
      have h4 : ∀ i < l, T[i]? ≠ a := by
        intro i hik
        by_cases hi : i + 1 < k
        · apply h3 at hi
          simp only [getElem?_cons_succ, ne_eq] at hi
          exact hi
        · unfold k at hi
          simp only [ge_iff_le, h2, add_lt_add_iff_right, not_lt] at hi
          contrapose hik
          exact Nat.not_lt.mpr hi
      apply idxOf?_getElem?_iff at h3
      apply idxOf?_getElem?_iff at h4
      simp [k, Nat.find_spec h] at h3
      rw [← h3]
      simp only [Option.map_some]
      rw [eq_comm] at h4
      simp_all

variable [BEq α] [LawfulBEq α]

theorem List.idxOf?_append {l₁ l₂ : List α} :
    idxOf? a (l₁ ++ l₂) = if a ∈ l₁ then idxOf? a l₁
    else (List.idxOf? a l₂).map (· + l₁.length) := by
    split <;> (rename_i h)
    <;> unfold idxOf?
    <;> rw [List.findIdx?_append]
    · refine Option.or_of_isSome ?_
      simp [h]
    · refine Option.or_of_isNone ?_
      simp only [findIdx?_isNone, beq_iff_eq, decide_not, all_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not]
      intro x h1
      exact ne_of_mem_of_not_mem h1 h


theorem idxOf?_length {α} [DecidableEq α] {a : α} {n : ℕ} {L : List α}
    (h : some n = idxOf? a L) : n < L.length :=
  sorry
  --isSome_getElem? (Option.isSome_of_mem (idxOf?_getElem? h))





@[simp]
theorem List.finIdxOf?_singleton {α : Type} [BEq α] {a b : α} :
    [a].finIdxOf? b = if a == b then some ⟨0, by simp⟩ else none := by
  simp [finIdxOf?]

theorem finIdxOf?_eq_pmap_idxOf? {α : Type} [BEq α] {xs : List α} {a : α} :
    xs.finIdxOf? a =
      (xs.idxOf? a).pmap
         (fun i m => by sorry)
        (fun i h => h) := sorry

@[grind =]
theorem finIdxOf?_append {α : Type} [BEq α] {xs ys : List α} {a : α} :
    (xs ++ ys).finIdxOf? a =
      ((xs.finIdxOf? a).map (Fin.castLE (by simp))).or
        ((ys.finIdxOf? a).map (Fin.natAdd xs.length) |>.map (Fin.cast (by simp))) := by sorry
/-   simp only [finIdxOf?_eq_pmap_idxOf?, idxOf?_append, Option.pmap_or]

  split <;> rename_i h _
  · simp [h, Option.pmap_map, Option.map_pmap, Nat.add_comm]
  · simp [h]
 -/
