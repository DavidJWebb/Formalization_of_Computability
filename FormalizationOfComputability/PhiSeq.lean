/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.List
import FormalizationOfComputability.Phi
import Mathlib.Data.List.TFAE
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Stream.Defs
import Mathlib.Tactic.TFAE

/- # Wₑ as a sequence
This file builds W_seq, which enumerates the elements n of W_e in the order that each ϕ_e(n) halts -/

namespace Computability

open Nat
open Nat.Partrec
open Nat.Partrec.Code
open List --hiding isSome_getElem?

/- The elements whose computations first halt at stage s, in increasing order. By definition,
these elements are less than s. -/
def PhiNewList (e s : ℕ) : List ℕ :=
  (range s).filter (λ n ↦ (Phi_s_halts e s n ∧ ¬ Phi_s_halts e (s-1) n))

def PhiNew (e s : ℕ) : Finset ℕ := (PhiNewList e s).toFinset

lemma PhiNewList_zero (e : ℕ) : PhiNewList e 0 = ∅ := by simp [PhiNewList]

variable {e s t n x y i k l : ℕ}

/- A helper lemma for moving between the list and set forms-/
lemma PhiNewList_mem (e s x : ℕ) : x ∈ PhiNewList e s ↔ x ∈ PhiNew e s := by
  simp [PhiNewList, PhiNew]

/- This lemma cleans up lines that would otherwise be a rather lengthy simp only -/
lemma PhiNew_mem_lemma (e s x : ℕ) :
    x ∈ PhiNew e s ↔ (x < s ∧ Phi_s_halts e s x ∧ ¬Phi_s_halts e (s - 1) x) := by
  simp [PhiNew, PhiNewList]

/- The elements newly halting at stage s are exactly W_{e, s} \ W_{e, s-1} -/
lemma PhiNew_eq_Ws_diff (e s : ℕ) : (PhiNew e s) = (W_s e s) \ (W_s e (s-1)) := by
  simp [PhiNew, W_s]
  apply subset_antisymm
  · intro x
    simp_all [PhiNewList]
  · intro x
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and, mem_toFinset,
      and_imp]
    intro h1 _ h3
    simp only [PhiNewList, Bool.decide_and, decide_not, mem_filter, mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    constructor
    · exact h1
    · simp_all only [true_and]
      contrapose h3
      simp_all only [Classical.not_imp, Decidable.not_not]
      simp only [(halt_input_bound h3), and_self]

/- Elements never enter twice - the PhiNew are disjoint -/
lemma PhiNew_disjoint_gt (e : ℕ) (h : s > t) :
    Disjoint (PhiNew e s) (PhiNew e t) := by
  rw [Finset.disjoint_iff_ne]
  simp only [PhiNew, PhiNewList, Bool.decide_and, decide_not, toFinset_filter, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Finset.mem_filter, mem_toFinset, mem_range, ne_eq, and_imp]
  intro a _ _ h1 b _ h2 _
  contrapose h1
  simp_all only [Decidable.not_not]
  apply phi_halts_mono (le_sub_one_of_lt h) h2

lemma PhiNew_pairwise_disjoint (e : ℕ) :
  Set.PairwiseDisjoint (Set.univ : Set ℕ) (PhiNew e) := by
  intro s _ t _ h
  rw [ne_iff_lt_or_gt] at h
  rcases h with h | h
  · exact Disjoint.symm (PhiNew_disjoint_gt e h)
  · exact PhiNew_disjoint_gt e h

/- If x is new at stage s, it is not in W_s (elements entering *before* s)-/
lemma PhiNew_is_new (e s : ℕ) : (PhiNew e s) ∩ (W_s e (s-1)) = ∅ := by simp [PhiNew_eq_Ws_diff]

/- It is sometimes useful to work with W_{e,s} instead of W_{e, s+1} -/
lemma Ws_eq (e s : ℕ) : W_s e s = (W_s e (s-1)) ∪ (PhiNew e s) := by
    rw [PhiNew_eq_Ws_diff]
    simp only [Finset.union_sdiff_self_eq_union, Finset.right_eq_union]
    apply W_s_mono
    simp

/- The new elements at stage s are exactly those with runtime s -/
lemma PhiNew_runtime_iff (e x r : ℕ) : x ∈ PhiNew e r ↔ r ∈ runtime e x := by
  constructor
  <;> intro h
  · rw [runtime_is_min]
    rw [PhiNew_mem_lemma] at h
    constructor
    · exact h.right.left
    · intro t h1
      exact phi_halts_mono_reverse (le_sub_one_of_lt h1) (h.right.right)
  · rw [runtime_is_min] at h
    rw [PhiNew_eq_Ws_diff]
    simp only [W_s, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and]
    have h1 : x < r + 1 := by
      apply halt_input_bound
      apply phi_halts_mono
      · linarith
      · exact h.left
    constructor
    · constructor
      · apply halt_input_bound
        exact h.left
      · exact h.left
    · intro h2
      apply Nat.ne_zero_of_lt at h2
      cases' r with r
      · tauto
      · simp only [add_tsub_cancel_right]
        apply h.right
        linarith

/- W_e can be created as a disjoint union of new elements-/
lemma We_eq_union_WsNew (e : ℕ) : W e = ⋃ s, (PhiNew e s) := by
  rw [W_eq_union_W_s]
  apply subset_antisymm
  <;> intro x h
  <;> simp_all only [Set.mem_iUnion, Finset.mem_coe]
  · obtain ⟨_, h⟩ := h
    apply Ws_runtime at h
    obtain ⟨r, h⟩ := h
    simp [PhiNew_runtime_iff]
    exact ⟨r, h.left⟩
  · obtain ⟨s, h⟩ := h
    rw [PhiNew_eq_Ws_diff] at h
    simp only [Finset.mem_sdiff] at h
    exact ⟨s, h.left⟩

/- TFAE :
Eventually all PhiNew e s = ∅
W_e is finite
There is an s such that W_e = W_{e, s}
-/

/- TODO : Move any implications not needed for lemmas to the TFAE -/
lemma PhiNew_stabilizes_implies_We_finite (e s : ℕ) (h : ∀ t > s, PhiNew e t = ∅) :
    (W e).Finite := by
  rw [We_eq_union_WsNew, Set.finite_iUnion_iff]
  · simp only [Finset.finite_toSet, implies_true, Finset.coe_nonempty, true_and]
    apply Set.Finite.subset (Set.finite_le_nat s)
    simp only [Set.setOf_subset_setOf]
    intro t h1
    contrapose h1
    simp_all
  · simp only [Finset.disjoint_coe]
    intro i j h1
    apply PhiNew_pairwise_disjoint
    <;> simp only [Set.mem_univ, ne_eq]
    exact h1

lemma We_finite_implies_PhiNew_stabilizes (e : ℕ) (h : (W e).Finite) :
    ∃ s, ∀ t > s, PhiNew e t = ∅ := by
  rw [We_eq_union_WsNew, Set.finite_iUnion_iff] at h
  simp only [Finset.finite_toSet, implies_true, Finset.coe_nonempty, true_and] at h
  have h1 := Set.Finite.exists_finset h
  obtain ⟨P, h1⟩ := h1
  · by_cases h2 : P = ∅
    · use 0
      simp_all
    · use Finset.max' P (Finset.nonempty_iff_ne_empty.mpr h2)
      intro s h3
      contrapose h3
      simp only [gt_iff_lt, Finset.max'_lt_iff, not_forall, Classical.not_imp, not_lt]
      use s
      simp only [le_refl, exists_prop, and_true, h1, Set.mem_setOf_eq]
      exact Finset.nonempty_iff_ne_empty.mpr h3
  · simp only [Finset.disjoint_coe]
    intro i j h1
    apply PhiNew_pairwise_disjoint
    <;> simp only [Set.mem_univ, ne_eq]
    exact h1

lemma We_finite_iff_PhiNew_stabilizes (e : ℕ) :
    (W e).Finite ↔ (∃ t, ∀ s > t, PhiNew e s = ∅) := by
  constructor
  · exact We_finite_implies_PhiNew_stabilizes e
  · intro ⟨_, h⟩
    exact PhiNew_stabilizes_implies_We_finite _ _ h

/- x appears as a new element at its runtime -/
lemma PhiNew_runtime (y e s : ℕ) : y ∈ PhiNew e s ↔ s ∈ runtime e y := by
  simp [runtime, rfindOpt]
  constructor
  <;> simp_all only [PhiNew_mem_lemma]
  · intro ⟨h, ⟨h1, h2⟩⟩
    constructor
    · obtain ⟨x, h1⟩ := h1
      exact Option.isSome_of_mem h1
    · intro m hm
      have h3 := halt_input_bound h1
      apply phi_halts_mono_reverse at h2
      · unfold Phi_s_halts at h2
        push_neg at h2
        exact Option.eq_none_iff_forall_ne_some.mpr h2
      · exact le_sub_one_of_lt hm
  · intro ⟨h, h1⟩
    apply Option.isSome_iff_exists.mp at h
    constructor
    · exact halt_input_bound h
    · constructor
      · exact h
      · unfold Phi_s_halts
        push_neg
        intro x
        by_cases h2 : s=0
        · simp [h2, Phi_s]
        · simp [h1, sub_one_lt, h2]

/- The elements in W_e enumerated up to stage s, in the order they appeared -/
def WPrefix (e : ℕ) : ℕ → List ℕ
    | 0     => []
    | s + 1 => (WPrefix e s) ++ (PhiNewList e (s+1))

/- WPrefix e s is exactly W_{e, s} in order of enumeration -/
lemma Ws_eq_prefix (e s : ℕ) : W_s e s = (WPrefix e s).toFinset := by
  induction' s with s hs
  · simp only [W_s, Finset.range_zero, Finset.filter_empty, WPrefix, toFinset_nil]
  · apply subset_antisymm
    intro y h
    simp only [WPrefix, toFinset_append, Finset.mem_union, mem_toFinset]
    by_cases h1 : y ∈ (W_s e s)
    · left
      simp only [← mem_toFinset, ← hs, h1]
    · right
      simp only [PhiNewList_mem, PhiNew_mem_lemma]
      simp [W_s] at h
      constructor
      · exact h.left
      · constructor
        · exact h.right
        · have h2 : Phi_s_halts e s y → y < s := halt_input_bound
          simp only [W_s, Finset.mem_filter, Finset.mem_range, not_and] at h1
          simp only [add_tsub_cancel_right]
          tauto
    · intro x h
      simp [WPrefix, PhiNew, W_s] at h
      rw [PhiNewList_mem, ← mem_toFinset, ← hs] at h
      simp only [W_s, Finset.mem_filter, Finset.mem_range]
      simp only [W_s, Finset.mem_filter, Finset.mem_range] at h
      rcases h with h | h
      · constructor
        · linarith
        · exact phi_halts_mono (Nat.le_add_right s 1) h.right
      · rw [PhiNew_eq_Ws_diff] at h
        simp only [W_s, add_tsub_cancel_right, Finset.mem_sdiff, Finset.mem_filter,
          Finset.mem_range, not_and] at h
        constructor
        <;> simp [h]

lemma WPrefix_mem (e s n : ℕ) : n ∈ WPrefix e s ↔ n ∈ W_s e s := by
  rw [← mem_toFinset, Ws_eq_prefix]

lemma WPrefix_phi (e n : ℕ) : (∃ s, n ∈ WPrefix e s) ↔ Phi_halts e n := by
  rw [phi_halts_stage_exists, exists_congr]
  intro a
  simp [← W_s_Phi_s, WPrefix_mem e a n]

/- Elements cannot be enumerated twice-/
lemma nodup_WPrefix (e s : ℕ) : Nodup (WPrefix e s) := by
  induction' s with s ih
  · simp [WPrefix]
  · simp only [WPrefix]
    apply List.Nodup.append ih
    · exact List.Nodup.filter _ nodup_range
    · unfold List.Disjoint
      simp only [PhiNewList_mem, PhiNew_eq_Ws_diff, Ws_eq_prefix, add_tsub_cancel_right,
        Finset.mem_sdiff, mem_toFinset]
      tauto

/- The WPrefixes are prefixes of each other-/
lemma WPrefix_mono (e s t : ℕ) (h : s ≤ t) :
  (WPrefix e s) <+: (WPrefix e t) := by
  induction' t with t ih
  · simp only [nonpos_iff_eq_zero] at h
    rw [h]
  · by_cases h1 : s = t + 1
    · rw [h1]
    · apply List.IsPrefix.trans (ih (le_of_lt_succ (lt_of_le_of_ne h h1)))
      simp [WPrefix]


/- It is often useful to view elements entering one at a time, so there may be a queue
of elements waiting to enter. This represents the elements still waiting *at* stage s,
i.e. the head of this list will be enumerated at stage s. -/
def enter_queue (e : ℕ) : ℕ → List ℕ
  | 0 => []
  | s + 1 => (enter_queue e s).tail ++ (PhiNewList e (s+1))

/- The element that has been emitted at stage s, if it exists -/
def new_element (e s : ℕ) : Option ℕ := (enter_queue e s).head?

/- The stage at which n is enumerated (if any).
Note that this is *not* the stage at which ϕ_e(n)↓, as n may wait in the enter_queue. -/
def enum_stage (e n : ℕ) : Part ℕ :=
  Nat.rfind (fun s => (new_element e s == some n))

/- The sequence of enumerated elements -/
def Wenum (e : ℕ) : Stream' (Option ℕ) := new_element e

/- If n is in the queue at stage s, then ϕ_{e, s}(n)↓ -/
lemma enter_queue_halts (h : n ∈ enter_queue e s) : Phi_s_halts e s n := by
  induction' s with s ih
  · tauto
  · simp only [enter_queue, List.mem_append] at h
    cases' h with h h
    · apply List.mem_of_mem_tail at h
      apply ih at h
      exact phi_halts_mono (Nat.le_add_right s 1) h
    · simp_all only [PhiNewList_mem, PhiNew_mem_lemma]

/- Elements of the queue are exactly the elements that halt -/
lemma enter_queue_mem (e n : ℕ) : (∃ s, n ∈ enter_queue e s) ↔ Phi_halts e n := by
  constructor
  · intro ⟨s, h⟩
    apply enter_queue_halts at h
    apply (phi_halts_stage_exists).mpr
    use s
  · intro h
    simp only [phi_halts_runtime_exists, ← PhiNew_runtime_iff] at h
    obtain ⟨r, h⟩ := h
    use r
    unfold enter_queue
    cases' r with r
    · tauto
    · simp only [mem_append]
      right
      simp [PhiNewList_mem, h]

/- A lemma for moving from (enter_queue e s) to (enter_queue e t) -/
lemma enter_queue_PhiNewList (e : ℕ) (h : s ≥ t) :
    (enter_queue e s) <:+
    (enter_queue e t) ++ flatten ((range (s - t)).map (λ i ↦ PhiNewList e (t + i + 1))) := by
  apply Nat.exists_eq_add_of_le at h
  obtain ⟨k, h⟩ := h
  revert s
  induction' k with k ih
  · simp_all
  · simp_all only [add_tsub_cancel_left, forall_eq, enter_queue, List.range_succ]
    have ih1 : (enter_queue e (t + k)).tail <:+
    enter_queue e t ++ (map (fun i ↦ PhiNewList e (t + i + 1)) (range k)).flatten := by
      apply IsSuffix.trans _ ih
      apply List.tail_suffix
    have ih2 : (enter_queue e (t + k)).tail ++ PhiNewList e (t + k + 1) <:+
    (enter_queue e t ++
    (map (fun i ↦ PhiNewList e (t + i + 1)) (range k)).flatten) ++ PhiNewList e (t + k + 1) := by
      obtain ⟨T, ih1⟩ := ih1
      use T
      rw [← append_assoc, ih1]
    simp_all

/- The queue at stage s is a suffix of WPrefix e s.
This is mostly here so that it's easy to show that enter queues have no duplicates -/
lemma enter_queue_WPrefix (e s : ℕ) :
    IsSuffix (enter_queue e s) (WPrefix e s) := by
  induction' s with s ih
  · simp [enter_queue]
  · unfold enter_queue WPrefix
    have h1 := List.IsSuffix.trans (tail_suffix (enter_queue e s)) ih
    cases' L : (enter_queue e s) with a T
    · simp
    · simp only [IsSuffix, L, tail_cons] at h1
      obtain ⟨S, h1⟩ := h1
      use S
      simp [← h1]

/- The queues have no duplicates. -/
lemma enter_queue_nodup (e s : ℕ) : Nodup (enter_queue e s) := by
  have ⟨_, h⟩ := enter_queue_WPrefix e s
  have h1 := nodup_WPrefix e s
  rw [← h] at h1
  exact List.Nodup.of_append_right h1

lemma enter_queue_nodup_elements (h : (enter_queue e s)[k]? = some n) (h1 : i ≠ k) :
    (enter_queue e s)[i]? ≠ some n := by
  by_contra h3
  rw [← h] at h3
  apply List.getElem?_inj at h3
  · tauto
  · rw [h] at h3
    refine List.isSome_getElem?.mp (Option.isSome_of_mem h3)
  · exact enter_queue_nodup e s

/- If n is not the head of an queue, then at the next step its index decreases by 1. -/
lemma enter_queue_dec_stage (h : n ∈ (enter_queue e s).tail) :
     List.idxOf? n (enter_queue e (s + 1)) = (List.idxOf? n (enter_queue e s)).map (· - 1) := by
  simp only [enter_queue, idxOf?_append, h, ↓reduceIte]
  cases' hL : enter_queue e s with a T
  · tauto
  · simp only [tail_cons]
    rw [index_tail] at h
    obtain ⟨k, ⟨h, h1⟩⟩ := h
    rw [← idxOf?_getElem?_iff] at h1
    · simp_all only [Option.map_some]
      have h3 : some k = idxOf? n ([a] ++ T) := by exact h1
      rw [List.idxOf?_append] at h3
      have h4 : n ∈ (a :: T).tail := by
        apply idxOf?_getElem? at h1
        apply index_tail.mpr
        use k
      have h5 : n ≠ a := by
        contrapose h
        simp only [ne_eq, Decidable.not_not] at h
        simp only [ge_iff_le, not_le, lt_one_iff]
        apply List.getElem?_inj (idxOf?_length h1)
        · rw [← hL]
          exact enter_queue_nodup e s
        · simp [idxOf?_getElem? h1, h]
      apply index_tail_minus_one at h4
      simp only [head?_cons, Option.some.injEq, h5, tail_cons, ← h1, Option.map_some,
        false_or] at h4
      simp [← h1, h4]
    · have h3 := enter_queue_nodup e s
      intro i hik
      apply enter_queue_nodup_elements h1
      linarith

/- If n is in the sth queue at position k, then for l≤k, it has index k-l in the (s+l)th queue -/
lemma enter_queue_dec (h : List.idxOf? n (enter_queue e s) = some k) (h1 : l ≤ k) :
    n ∈ enter_queue e (s+l) ∧ List.idxOf? n (enter_queue e (s+l)) = some (k - l) := by
  have h2 := idxOf?_mem (id (Eq.symm h))
  have h3 := h2
  apply ne_nil_of_mem at h2
  apply ne_nil_iff_exists_cons.mp at h2
  obtain ⟨a, ⟨T, h2⟩⟩ := h2
  rw [h2] at h
  revert n
  induction' l with l ih
  · simp_all
  · intro n hn hk
    have ⟨h3, h4⟩ : n ∈ enter_queue e (s + l) ∧ idxOf? n (enter_queue e (s + l)) = some (k - l) := by
      apply ih (le_of_succ_le h1)
      simp_all only [mem_cons, forall_eq_or_imp]
      exact hk
    have h5 : n ∈ (enter_queue e (s + l)).tail := by
      rw [index_tail]
      use k-l
      constructor
      · exact Nat.le_sub_of_add_le' h1
      · exact idxOf?_getElem? h4.symm
    constructor
    · simp [enter_queue, h5]
    · apply enter_queue_dec_stage at h5
      simp [← add_assoc, h5]
      use k-l
      constructor
      · exact h4
      · rfl

/- If n is in the sth queue at position k, it is enumerated at stage s+k -/
lemma enter_queue_enum_exact (h : List.idxOf? n (enter_queue e s) = some k) :
    new_element e (s+k) = n := by
  have h1 : k ≤ k := by rfl
  apply enter_queue_dec at h
  apply h at h1
  simp only [tsub_self] at h1
  obtain ⟨_, h1⟩ := h1
  rw [eq_comm, new_element, index_head, ← idxOf?_getElem?_iff]
  · exact id (Eq.symm h1)
  · tauto

/- If n is in a queue, it is eventually enumerated -/
lemma enter_queue_enum (h : n ∈ (enter_queue e s)) :
    ∃ t, new_element e t = n := by
  have ⟨k, h1⟩ : ∃ k, List.idxOf? n (enter_queue e s) = some k :=
    Option.isSome_iff_exists.mp (isSome_idxOf?.mpr h)
  apply enter_queue_enum_exact at h1
  use s+k

/- If n is in the sth queue at position k, it is in no queue after the (s+k)th -/
lemma enter_queue_exit_exact (h : List.idxOf? n (enter_queue e s) = some k) :
    ∀ t, n ∉ enter_queue e (s + k + t + 1) := by
  intro t
  have h1 := idxOf?_mem (id (Eq.symm h))
  have h2 := enter_queue_enum_exact h
  have ⟨r, ⟨h3, _⟩⟩ := runtime_is_min' (enter_queue_halts h1)
  rw [← PhiNew_runtime_iff] at h3
  induction' t with t ih
  <;> nth_rw 1 [enter_queue]
  <;> simp only [mem_append, not_or]
  · constructor
    · cases' hL : enter_queue e (s+k) with a T
      · simp_all
      · have h4 := enter_queue_nodup e (s+k)
        have h5 := enter_queue_enum_exact h
        unfold new_element at h5
        simp_all
    · have h4 : Disjoint (PhiNew e r) (PhiNew e (s+k+1)) := by
        refine Disjoint.symm (PhiNew_disjoint_gt e ?_)
        linarith
      rw [Finset.disjoint_left] at h4
      rw [PhiNewList_mem]
      exact h4 h3
  · constructor
    · contrapose ih
      simp_all only [Decidable.not_not]
      exact mem_of_mem_tail ih
    · have h4 : Disjoint (PhiNew e r) (PhiNew e (s+k+t+2)) := by
        refine Disjoint.symm (PhiNew_disjoint_gt e ?_)
        linarith
      rw [Finset.disjoint_left] at h4
      rw [PhiNewList_mem]
      exact h4 h3

/- If n is in a queue, eventually it is never in a queue again -/
lemma enter_queue_exit (h : n ∈ (enter_queue e s)) :
    ∃ s₁, ∀ t > s₁, n ∉ enter_queue e t := by
  have ⟨k, h1⟩ : ∃ k, List.idxOf? n (enter_queue e s) = some k :=
    Option.isSome_iff_exists.mp (isSome_idxOf?.mpr h)
  apply enter_queue_exit_exact at h1
  use s+k+1
  intro t₁ ht1
  have ⟨l, ht2⟩ : ∃ l, t₁ = s + k + 1 + l := by
    refine Nat.exists_eq_add_of_le ?_
    linarith
  have ht3 := h1 l
  have ht4 : s + k + 1 + l = s + k + l + 1 := by linarith
  simp_all

lemma Phi_halts_Wenum (e n : ℕ) : Phi_halts e n ↔ ∃ s, n = Wenum e s := by
  rw [← enter_queue_mem]
  unfold Wenum
  constructor
  <;> intro ⟨s, h⟩
  · apply enter_queue_enum at h
    obtain ⟨t, h⟩ := h
    use t
    simp [h]
  · unfold new_element at h
    exact ⟨s, mem_of_mem_head? h.symm⟩

/-- TODO: prove a constructive version, then generalize to exists -/
/- If PhiNew stabilizes, then eventually the queue depletes.
Indeed iff is true, see TFAE below. -/
lemma queue_depletes (h : (W e).Finite) :
    ∃ t, ∀ s > t, enter_queue e s = [] := by
  rw [We_finite_iff_PhiNew_stabilizes] at h
  obtain ⟨t, h⟩ := h -- unfortunately the queue at stage t may not be empty
  use t+(enter_queue e t).length
  intro s _
  have hx : ∀ x, x ∈ enter_queue e t → x ∉ enter_queue e s := by
    intro x h
    have ⟨k, hxk⟩ := Option.isSome_iff_exists.mp (isSome_idxOf?.mpr h)
    have hkl := idxOf?_length hxk.symm
    apply enter_queue_exit_exact at hxk
    have ⟨k1, hsk1⟩ : ∃ k1, s = t + k + k1 + 1 := by
      apply Nat.exists_eq_add_of_lt
      linarith
    rw [hsk1]
    exact hxk k1
  have hs : s ≥ t := by linarith
  have hs1 := enter_queue_PhiNewList e hs
  have hi : ∀ i, PhiNew e (t+i+1) = ∅ := by
    intro i
    apply h
    linarith
  have hi1 : ∀ i, PhiNewList e (t+i+1) = [] := by
    intro i
    rw [← toFinset_eq_empty_iff]
    exact hi i
  simp_all only [gt_iff_lt, ge_iff_le, map_const', length_range, flatten_replicate_nil, append_nil]
  apply IsSuffix.subset at hs1
  rw [← toFinset_eq_empty_iff]
  ext x
  simp only [mem_toFinset, Finset.notMem_empty, iff_false]
  intro h
  have h1 := hs1 h
  apply hx at h1
  tauto

lemma Wenum_finite_iff (e : ℕ) : (W e).Finite ↔ ∃ s, ∀ t > s, Wenum e t = Option.none := by
  constructor
  · intro h
    have ⟨s, h1⟩ := queue_depletes h
    use s
    intro t ht
    simp_all only [Wenum, new_element, head?_eq_none_iff, gt_iff_lt]
  · rw [We_finite_iff_PhiNew_stabilizes]
    intro ⟨t, h⟩
    use t
    intro s h1
    simp only [gt_iff_lt, Wenum, new_element, head?_eq_none_iff] at h
    have h2 : enter_queue e s = [] := by simp_all
    unfold enter_queue at h2
    cases' s with s
    · tauto
    · simp only [append_eq_nil_iff] at h2
      ext x
      simp [← PhiNewList_mem, h2]

lemma Wenum_infinite_iff (e : ℕ) : (W e).Infinite ↔ ∀ s, ∃ t > s, ∃ n, Wenum e t = some n := by
  have h := Wenum_finite_iff e
  have h1 : ¬ (W e).Finite ↔ (W e).Infinite := Iff.symm (Eq.to_iff rfl)
  simp_all [Option.ne_none_iff_exists']

-- the following are here just to prove the TFAE statement
lemma queue_depletes_implies_PhiNew_stabilizes (h : ∃ t, ∀ s > t, enter_queue e s = []) :
    ∃ t, ∀ s > t, PhiNew e s = ∅ := by
  obtain ⟨t, h⟩ := h
  use t
  intro s hts
  have h1 := h s hts
  by_cases hs : s = 0
  · simp [hs]
    rfl
  · obtain ⟨k, hs1⟩ := exists_eq_succ_of_ne_zero hs
    rw [hs1] at h1
    unfold enter_queue at h1
    apply List.append_eq_nil_iff.mp at h1
    simp [PhiNew]
    simp [h1, hs1]

lemma Ws_stabilizes_implies_We_eq_Ws (h : ∃ t, ∀ s > t, W_s e s = W_s e t) :
    ∃ t, W e = W_s e t := by
  obtain ⟨t, h⟩ := h
  use t
  ext x
  rw [W_mem_iff_W_s]
  constructor
  <;> intro h1
  · obtain ⟨s, h1⟩ := h1
    by_cases hts : s > t
    · apply h at hts
      simp [← hts, h1]
    · exact W_s_mono (Nat.le_of_not_lt hts) h1
  · use t
    exact h1

lemma We_finite_iff_We_eq_Ws (h : ∃ t, W e = W_s e t) : (W e).Finite := by
  obtain ⟨t, h⟩ := h
  rw [h]
  simp

lemma WsNew_stabilizes_Ws_stabilizes (e : ℕ) (h : ∃ t, ∀ s > t, PhiNew e s = ∅) :
    ∃ t, ∀ s > t, W_s e s = W_s e t := by
  obtain ⟨t, h⟩ := h
  use t
  intro s
  have h1 : ∀ s > t, W_s e s = W_s e (s-1) := by
    intro s h1
    induction' s with s ih
    · tauto
    · simp
      apply h at h1
      rw [PhiNew_eq_Ws_diff] at h1
      simp at h1
      exact subset_antisymm h1 (W_s_mono_reverse (Nat.le_add_right s 1))
  induction' s with s ih
  · tauto
  · intro h2
    have h3 := h2
    apply h1 at h2
    simp at h2
    rw [h2]
    by_cases h4 : s > t
    · simp [ih, h4]
    · have h5 := Eq.symm (Nat.eq_of_lt_succ_of_not_lt h3 h4)
      rw [h5]

theorem We_finite_TFAE (e : ℕ) :
    [(W e).Finite,                          --1
      ∃ t, ∀ s > t, PhiNew e s = ∅,         --2
      ∃ t, ∀ s > t, W_s e s = W_s e t,      --3
      ∃ t, W e = W_s e t,                   --4
      ∃ t, ∀ s > t, enter_queue e s = [],   --5
      ∃ t, ∀ s > t, Wenum e s = Option.none --6
    ].TFAE := by
  tfae_have 1 → 5 := queue_depletes
  tfae_have 5 → 2 := queue_depletes_implies_PhiNew_stabilizes
  tfae_have 2 → 3 := WsNew_stabilizes_Ws_stabilizes e
  tfae_have 3 → 4 := Ws_stabilizes_implies_We_eq_Ws
  tfae_have 4 → 1 := We_finite_iff_We_eq_Ws
  tfae_have 1 ↔ 6 := Wenum_finite_iff e
  tfae_finish
