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
  (range s).filter (λ n => (Phi_s_halts e s n ∧ ¬ Phi_s_halts e (s-1) n))

def PhiNew (e s : ℕ) : Finset ℕ := (PhiNewList e s).toFinset

lemma PhiNewList_zero (e : ℕ) : PhiNewList e 0 = ∅ := by
  simp [PhiNewList]

/- A helper lemma for moving between the list and set forms-/
lemma PhiNewList_mem (e s x : ℕ) : x ∈ PhiNewList e s ↔ x ∈ PhiNew e s := by
  constructor
  · simp [PhiNewList, PhiNew]
  · simp [PhiNew]

/- The elements newly halting at stage s are exactly W_{e, s} \ W_{e, s-1} -/
lemma PhiNew_eq_Ws_diff (e s : ℕ) : (PhiNew e s) = (W_s e s) \ (W_s e (s-1)) := by
  simp [PhiNew, W_s]
  apply subset_antisymm
  · intro x
    simp_all [PhiNewList]
  · intro x
    simp
    intro h1 h2 h3
    simp_all [PhiNewList]
    contrapose h3
    simp_all
    have h4 : x < s - 1 := by exact halt_input_bound e (s-1) x h3
    exact add_lt_of_lt_sub h4

/- Elements never enter twice - the PhiNew are disjoint -/
lemma PhiNew_disjoint_gt (e s t : ℕ) (h : s > t) :
    Disjoint (PhiNew e s) (PhiNew e t) := by
  rw [Finset.disjoint_iff_ne]
  simp [PhiNew, PhiNewList]
  intro a _ _ h1 b _ h2 _
  contrapose h1
  simp
  simp at h1
  simp [← h1] at h2
  apply phi_halts_mono e t
  · cases' s with s
    · tauto
    · exact le_sub_one_of_lt h
  · exact h2

lemma PhiNew_pairwise_disjoint (e : ℕ) :
  Set.PairwiseDisjoint (Set.univ : Set ℕ) (PhiNew e) := by
  intro s _ t _ h
  rw [ne_iff_lt_or_gt] at h
  rcases h with h | h
  · exact Disjoint.symm (PhiNew_disjoint_gt e t s h)
  · exact PhiNew_disjoint_gt e s t h

/- If x is new at stage s, it is not in W_s (elements entering *before* s)-/
lemma PhiNew_is_new (e s : ℕ) : (PhiNew e s) ∩ (W_s e (s-1)) = ∅ := by
  rw [PhiNew_eq_Ws_diff]
  simp

/- It is sometimes useful to work with W_{e,s} instead of W_{e, s+1} -/
lemma Ws_eq (e s : ℕ) : W_s e s = (W_s e (s-1)) ∪ (PhiNew e s) := by
    rw [PhiNew_eq_Ws_diff]
    simp
    apply W_s_mono
    simp

/- The new elements at stage s are exactly those with runtime s -/
lemma PhiNew_runtime_iff (e x r : ℕ) : x ∈ PhiNew e r ↔ r ∈ runtime e x := by
  constructor
  <;> intro h
  · rw [runtime_is_min]
    simp [PhiNew, PhiNewList] at h
    constructor
    · exact h.right.left
    · intro t h1
      apply phi_halts_mono_reverse e t (r-1)
      · exact le_sub_one_of_lt h1
      · exact h.right.right
  · rw [runtime_is_min] at h
    rw [PhiNew_eq_Ws_diff]
    simp [W_s]
    have h1 : x < r + 1 := by
      apply halt_input_bound e
      apply phi_halts_mono e r (r+1)
      · linarith
      · exact h.left
    constructor
    · constructor
      · apply halt_input_bound e
        exact h.left
      · exact h.left
    · intro h2
      apply Nat.ne_zero_of_lt at h2
      cases' r with r
      · tauto
      · simp
        rw [← Phi_s_diverges]
        apply h.right
        linarith

/- W_e can be created as a disjoint union of new elements-/
lemma We_eq_union_WsNew (e : ℕ) : W e = ⋃ s, (PhiNew e s) := by
  rw [W_eq_union_W_s]
  apply subset_antisymm
  · intro x h
    simp at h
    obtain ⟨s, h⟩ := h
    apply Ws_runtime at h
    obtain ⟨r, ⟨h, h1⟩⟩ := h
    simp
    use r
    rw [PhiNew_runtime_iff]
    exact h
  · intro x h
    simp at h
    obtain ⟨s, h⟩ := h
    rw [PhiNew_eq_Ws_diff] at h
    simp
    use s
    simp at h
    exact h.left

/- If eventually no new elements ever enter, then W_{e, s} never again changes-/
lemma WsNew_stabilizes_Ws_stabilizes (e t : ℕ) (h : ∀ s ≥ t, PhiNew e s = ∅) :
    ∀ s ≥ t, W_s e s = W_s e t := by
  have h1 : ∀ s ≥ t, (W_s e (s+1)) = (W_s e s) := by
    intro s h1
    rw [Ws_eq]
    simp
    have h2 : PhiNew e (s+1) = ∅ := by
      apply h
      linarith
    rw [h2]
    simp
  intro s h2
  induction' s using Nat.strong_induction_on with s ih
  by_cases h3 : s = t
  · simp [h3]
  · have h4 : s-1 ≥ t := by
      refine le_sub_one_of_lt ?_
      exact Nat.lt_of_le_of_ne h2 fun a ↦ h3 (id (Eq.symm a))
    have h5 : (W_s e (s-1)) = (W_s e t) := by
      apply ih (s-1)
      · apply Nat.sub_one_lt
        cases t
        · tauto
        · linarith
      exact h4
    rw [← h5]
    have h6 : W_s e ((s - 1) + 1) = (W_s e (s-1)) := by
      exact h1 (s - 1) h4
    have h7 : s - 1 + 1 = s := by
      refine Nat.sub_add_cancel ?_
      cases t
      · exact one_le_iff_ne_zero.mpr h3
      · exact one_le_of_lt h2
    rw [h7] at h6
    exact h6




/- TFAE :
Eventually all PhiNew e s = ∅
W_e is finite
There is an s such that W_e = W_{e, s}
-/

/- TODO : Move any implications not needed for lemmas to the TFAE -/
lemma PhiNew_stabilizes_implies_We_finite (e s : ℕ) (h : ∀ t > s, PhiNew e t = ∅) :
    (W e).Finite := by
  rw [We_eq_union_WsNew, Set.finite_iUnion_iff]
  · simp
    apply Set.Finite.subset (Set.finite_le_nat s)
    simp
    intro t h1
    contrapose h1
    simp_all
  · simp
    intro i j h1
    apply PhiNew_pairwise_disjoint
    <;> simp
    exact h1

lemma PhiNew_stabilizes_implies_We_eq_Ws (e s : ℕ) (h : ∀ t > s, PhiNew e t = ∅) :
    W e = W_s e s := by
  rw [We_eq_union_WsNew]
  apply subset_antisymm
  · intro x h1
    simp at h1
    obtain ⟨r, h1⟩ := h1
    have h2 : r ≤ s := by
      contrapose h1
      simp at h1
      apply h at h1
      rw [h1]
      simp
    have h3 : x ∈ W_s e r := by
      rw [Ws_eq]
      exact Finset.mem_union_right (W_s e (r - 1)) h1
    apply W_s_mono e r
    · exact h2
    · exact h3
  · intro x h1
    apply Ws_runtime at h1
    obtain ⟨r, ⟨h1, h2⟩⟩ := h1
    rw [← PhiNew_runtime_iff] at h1
    simp
    use r

lemma We_finite_implies_PhiNew_stabilizes (e : ℕ) (h : (W e).Finite) :
    ∃ s, ∀ t > s, PhiNew e t = ∅ := by
  rw [We_eq_union_WsNew, Set.finite_iUnion_iff] at h
  simp at h
  have h1 :  ∃ P : Finset ℕ, ∀ n, n ∈ P ↔ n ∈ {i | (PhiNew e i).Nonempty} := by
    apply Set.Finite.exists_finset h
  obtain ⟨P, h1⟩ := h1
  · by_cases h2 : P = ∅
    · use 0
      intro s h3
      rw [h2] at h1
      simp at h1
      apply h1
    · let N := Finset.max' P (Finset.nonempty_iff_ne_empty.mpr h2)
      use N
      intro s h3
      contrapose h3
      simp
      push_neg at h3
      have h4 : s ∈ P := by
        rw [h1]
        simp
        exact Finset.nonempty_iff_ne_empty.mpr h3
      simp [lt_iff_add_one_le]
      exact Finset.le_max' P s h4
  · simp
    intro i j h1
    apply PhiNew_pairwise_disjoint
    <;> simp
    exact h1

lemma We_finite_iff_PhiNew_stabilizes (e : ℕ) :
    (W e).Finite ↔ (∃ t, ∀ s > t, PhiNew e s = ∅) := by
  constructor
  · apply We_finite_implies_PhiNew_stabilizes e
  · intro ⟨t, h⟩
    apply PhiNew_stabilizes_implies_We_finite
    exact h

lemma We_finite_iff_We_eq_Ws (e : ℕ) : (W e).Finite ↔ ∃ s, W e = W_s e s := by
  constructor
  · rw [We_finite_iff_PhiNew_stabilizes]
    intro ⟨t, h⟩
    use t
    apply PhiNew_stabilizes_implies_We_eq_Ws
    exact h
  · intro ⟨s, h⟩
    rw [h]
    simp

/- x appears as a new element at its runtime -/
lemma PhiNew_runtime (y e s : ℕ) : y ∈ PhiNew e s ↔ s ∈ runtime e y := by
  simp [runtime, rfindOpt]
  constructor
  · simp [PhiNew, PhiNewList, W_s]
    intro h h1 h2
    constructor
    · exact Option.isSome_iff_exists.mpr h1
    · intro m hm
      have h3 : Phi_s_halts e s y → y < s := by
        apply halt_input_bound
      apply phi_halts_mono_reverse e m at h2
      · unfold Phi_s_diverges Phi_s_halts at h2
        push_neg at h2
        exact Option.eq_none_iff_forall_ne_some.mpr h2
      · exact le_sub_one_of_lt hm
  · intro ⟨h, h1⟩
    apply Option.isSome_iff_exists.mp at h
    simp [PhiNew, PhiNewList]
    constructor
    · apply halt_input_bound e
      simp [Phi_s_halts, h]
    · constructor
      · exact h
      · unfold Phi_s_halts
        push_neg
        intro y
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
  · simp [WPrefix, W_s]
  · apply subset_antisymm
    intro y h
    simp [WPrefix]
    by_cases h1 : y ∈ (W_s e s)
    · left
      rw [← mem_toFinset, ← hs]
      exact h1
    · right
      simp [PhiNew, PhiNewList]
      simp [W_s] at h
      constructor
      · exact h.left
      · constructor
        · exact h.right
        · have h2 : Phi_s_halts e s y → y < s := by
            apply halt_input_bound
          simp [W_s] at h1
          tauto
    · intro x h
      simp [WPrefix, PhiNew, W_s] at h
      rw [PhiNewList_mem, ← mem_toFinset, ← hs] at h
      simp [W_s]
      simp [W_s] at h
      rcases h with h | h
      · constructor
        · linarith
        · apply phi_halts_mono e s
          · linarith
          · exact h.right
      · rw [PhiNew_eq_Ws_diff] at h
        simp [W_s] at h
        constructor
        · exact h.left.left
        · exact h.left.right

lemma WPrefix_mem (e s n : ℕ) : n ∈ WPrefix e s ↔ n ∈ W_s e s := by
  rw [← mem_toFinset, Ws_eq_prefix]

lemma WPrefix_phi (e n : ℕ) : (∃ s, n ∈ WPrefix e s) ↔ Phi_halts e n := by
  rw [phi_halts_stage_exists, exists_congr]
  intro a
  rw [← W_s_Phi_s]
  exact WPrefix_mem e a n

/- Elements cannot be enumerated twice-/
lemma nodup_WPrefix (e s : ℕ) : Nodup (WPrefix e s) := by
  induction' s with s ih
  · unfold WPrefix
    simp
  · simp [WPrefix]
    apply List.Nodup.append
    · exact ih
    · apply List.Nodup.filter
      exact nodup_range
    · unfold List.Disjoint
      intro a h h1
      simp [PhiNewList_mem, PhiNew_eq_Ws_diff, Ws_eq_prefix] at h1
      obtain ⟨h1, h2⟩ := h1
      tauto

/- The WPrefixes are prefixes of each other-/
lemma WPrefix_mono (e s t : ℕ) (h : s ≤ t) :
  (WPrefix e s) <+: (WPrefix e t) := by
  induction' t with t ih
  · simp at h
    rw [h]
  · by_cases h1 : s = t + 1
    · rw [h1]
    · have h2 : s ≤ t := by
        exact le_of_lt_succ (lt_of_le_of_ne h h1)
      apply ih at h2
      apply List.IsPrefix.trans h2
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
lemma enter_queue_halts (e s n: ℕ) (h : n ∈ enter_queue e s) : Phi_s_halts e s n := by
  induction' s with s ih
  · tauto
  · unfold enter_queue at h
    rw [List.mem_append] at h
    cases' h with h h
    · apply List.mem_of_mem_tail at h
      apply ih at h
      exact phi_halts_mono e s (s+1) n (Nat.le_add_right s 1) h
    · simp [PhiNewList] at h
      exact h.right.left

/- Elements of the queue are exactly the elements that halt -/
lemma enter_queue_mem (e n : ℕ) : (∃ s, n ∈ enter_queue e s) ↔ Phi_halts e n := by
  constructor
  · intro ⟨s, h⟩
    apply enter_queue_halts at h
    apply (phi_halts_stage_exists e n).mpr
    use s
  · intro h
    simp [phi_halts_runtime_exists, ← PhiNew_runtime_iff] at h
    obtain ⟨r, h⟩ := h
    use r
    unfold enter_queue
    cases' r with r
    · tauto
    · simp
      right
      simp [PhiNewList_mem, h]

/- A lemma for moving from (enter_queue e s) to (enter_queue e t) -/
lemma enter_queue_PhiNewList (e t s : ℕ) (h : s ≥ t) :
    (enter_queue e s) <:+
    (enter_queue e t) ++ flatten ((range (s - t)).map (λ i => PhiNewList e (t + i + 1))) := by
  apply Nat.exists_eq_add_of_le at h
  obtain ⟨k, h⟩ := h
  revert s
  induction' k with k ih
  · simp_all
  · simp_all
    rw [← add_assoc]
    dsimp [enter_queue]
    rw [List.range_succ]
    have ih1 : (enter_queue e (t + k)).tail <:+
    enter_queue e t ++ (map (fun i ↦ PhiNewList e (t + i + 1)) (range k)).flatten := by
      apply IsSuffix.trans
      apply List.tail_suffix
      exact ih
    clear ih
    have ih2 : (enter_queue e (t + k)).tail ++ PhiNewList e (t + k + 1) <:+
    (enter_queue e t ++
    (map (fun i ↦ PhiNewList e (t + i + 1)) (range k)).flatten) ++ PhiNewList e (t + k + 1) := by
      obtain ⟨T, ih1⟩ := ih1
      use T
      rw [← append_assoc, ih1]
    simp_all

/- The queue at stage s is a suffix of WPrefix e s.
This is mostly here to make the next lemma easy -/
lemma enter_queue_WPrefix (e s : ℕ) :
    IsSuffix (enter_queue e s) (WPrefix e s) := by
  induction' s with s ih
  · simp [enter_queue]
  · unfold enter_queue WPrefix
    have h1 : (enter_queue e s).tail <:+ WPrefix e s := by
      apply List.IsSuffix.trans (tail_suffix (enter_queue e s)) ih
    cases' L : (enter_queue e s) with a T
    · simp
    · simp [L, IsSuffix] at h1
      obtain ⟨S, h1⟩ := h1
      use S
      simp [← h1]

/- The queues have no duplicates. -/
lemma enter_queue_nodup (e s : ℕ) : Nodup (enter_queue e s) := by
  have ⟨L, h⟩ := enter_queue_WPrefix e s
  have h1 := nodup_WPrefix e s
  rw [← h] at h1
  exact List.Nodup.of_append_right h1

lemma enter_queue_nodup_elements (e s k i n : ℕ) (h : (enter_queue e s)[k]? = some n) (h1 : i ≠ k) :
    (enter_queue e s)[i]? ≠ some n := by
  by_contra h3
  rw [← h] at h3
  apply List.getElem?_inj at h3
  · tauto
  · rw [h] at h3
    refine List.isSome_getElem?.mp ?_
    exact Option.isSome_of_mem h3
  · exact enter_queue_nodup e s

/- If n is not the head of an queue, then at the next step its index decreases by 1. -/
lemma enter_queue_dec_stage (e n s : ℕ)
    (h : n ∈ (enter_queue e s).tail) :
     List.idxOf? n (enter_queue e (s + 1)) = (List.idxOf? n (enter_queue e s)).map (· - 1) := by
  dsimp [enter_queue]
  simp [List.idxOf?_append, h]
  cases' hL : enter_queue e s with a T
  · tauto
  · simp
    rw [index_tail] at h
    obtain ⟨k, ⟨h, h1⟩⟩ := h
    rw [← idxOf?_getElem?_iff] at h1
    · rw [hL] at h1
      rw [← h1]
      simp
      have h3 : some k = idxOf? n ([a] ++ T) := by exact h1
      rw [List.idxOf?_append] at h3
      have h4 : n ∈ (a :: T).tail := by
        apply idxOf?_getElem? at h1
        apply index_tail.mpr
        use k
      have h5 : n ≠ a := by
        contrapose h
        simp at h
        simp
        have h2 := idxOf?_length h1
        apply List.getElem?_inj h2
        · rw [← hL]
          exact enter_queue_nodup e s
        · rw [idxOf?_getElem? h1]
          simp [h]
      apply index_tail_minus_one at h4
      simp [h5, ← h1] at h4
      exact h4
    · have h3 := enter_queue_nodup e s
      intro i hik
      apply enter_queue_nodup_elements e s k i n h1
      linarith

/- If n is in the sth queue at position k, then for l≤k, it has index k-l in the (s+l)th queue -/
lemma enter_queue_dec (e n s k l : ℕ) (h : List.idxOf? n (enter_queue e s) = some k) (h1 : l ≤ k) :
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
      simp_all
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
lemma enter_queue_enum_exact (e s n k : ℕ) (h : List.idxOf? n (enter_queue e s) = some k) :
    new_element e (s+k) = n := by
  have h1 : k ≤ k := by rfl
  apply enter_queue_dec at h
  apply h at h1
  simp at h1
  obtain ⟨h1, h2⟩ := h1
  rw [eq_comm, new_element, index_head, ← idxOf?_getElem?_iff]
  · exact id (Eq.symm h2)
  · tauto

/- If n is in a queue, it is eventually enumerated -/
lemma enter_queue_enum (e s n : ℕ) (h : n ∈ (enter_queue e s)) :
    ∃ t, new_element e t = n := by
  have ⟨k, h1⟩ : ∃ k, List.idxOf? n (enter_queue e s) = some k := by
    refine Option.isSome_iff_exists.mp ?_
    exact isSome_idxOf?.mpr h
  apply enter_queue_enum_exact at h1
  use s+k

/- If n is in the sth queue at position k, it is in no queue after the (s+k)th -/
lemma enter_queue_exit_exact (e s n k : ℕ) (h : List.idxOf? n (enter_queue e s) = some k) :
    ∀ t, n ∉ enter_queue e (s + k + t + 1) := by
  intro t
  have h1 := idxOf?_mem (id (Eq.symm h))
  have h2 := enter_queue_enum_exact e s n k h
  have ⟨r, ⟨h3, h4⟩⟩ := runtime_is_min' e s n (enter_queue_halts e s n h1)
  rw [← PhiNew_runtime_iff] at h3
  induction' t with t ih
  <;> nth_rw 1 [enter_queue]
  <;> simp
  · constructor
    · cases' hL : enter_queue e (s+k) with a T
      · simp_all
      · have h3 := enter_queue_nodup e (s+k)
        have h4 := enter_queue_enum_exact e s n k h
        unfold new_element at h4
        simp_all
    · have h5 : Disjoint (PhiNew e r) (PhiNew e (s+k+1)) := by
        refine Disjoint.symm (PhiNew_disjoint_gt e (s + k + 1) r ?_)
        linarith
      rw [Finset.disjoint_left] at h5
      rw [PhiNewList_mem]
      apply h5 h3
  · constructor
    · contrapose ih
      simp_all
      exact mem_of_mem_tail ih
    · have h5 : Disjoint (PhiNew e r) (PhiNew e (s+k+t+2)) := by
        refine Disjoint.symm (PhiNew_disjoint_gt e (s+k+t+2) r ?_)
        linarith
      rw [Finset.disjoint_left] at h5
      rw [PhiNewList_mem]
      apply h5 h3

/- If n is in a queue, eventually it is never in a queue again -/
lemma enter_queue_exit (e s n : ℕ) (h : n ∈ (enter_queue e s)) :
    ∃ s₁, ∀ t > s₁, n ∉ enter_queue e t := by
  have ⟨k, h1⟩ : ∃ k, List.idxOf? n (enter_queue e s) = some k := by
    refine Option.isSome_iff_exists.mp ?_
    exact isSome_idxOf?.mpr h
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
    use s
    exact mem_of_mem_head? h.symm

/- If PhiNew stabilizes, then eventually the queue depletes.
Indeed iff is true, see TFAE below. -/
lemma queue_depletes (e : ℕ) (h : (W e).Finite) :
    ∃ t, ∀ s > t, enter_queue e s = [] := by
  rw [We_finite_iff_PhiNew_stabilizes] at h
  obtain ⟨t, h⟩ := h -- unfortunately the queue at stage t may not be empty
  let l := (enter_queue e t).length
  use t+l
  intro s hs
  have hx : ∀ x, x ∈ enter_queue e t → x ∉ enter_queue e s := by
    intro x h
    have ⟨k, hxk⟩ := Option.isSome_iff_exists.mp (isSome_idxOf?.mpr h)
    have hkl : k < l := idxOf?_length hxk.symm
    apply enter_queue_exit_exact at hxk
    have ⟨k1, hsk1⟩ : ∃ k1, s = t + k + k1 + 1 := by
      apply Nat.exists_eq_add_of_lt
      linarith
    rw [hsk1]
    exact hxk k1
  have hs : s ≥ t := by linarith
  have hs1 := enter_queue_PhiNewList e t s hs
  have hi : ∀ i, PhiNew e (t+i+1) = ∅ := by
    intro i
    apply h
    linarith
  have hi1 : ∀ i, PhiNewList e (t+i+1) = [] := by
    intro i
    rw [← toFinset_eq_empty_iff]
    exact hi i
  simp_all
  apply IsSuffix.subset at hs1
  rw [← toFinset_eq_empty_iff]
  ext x
  simp
  intro h
  have h1 := hs1 h
  apply hx at h1
  tauto

lemma Wenum_finite_iff (e : ℕ) : (W e).Finite ↔ ∃ s, ∀ t > s, Wenum e t = Option.none := by
  constructor
  · intro h
    have ⟨s, h1⟩ := queue_depletes e h
    use s
    intro t ht
    simp [Wenum, new_element]
    simp_all
  · rw [We_finite_iff_PhiNew_stabilizes]
    intro ⟨t, h⟩
    use t
    intro s h1
    simp [Wenum, new_element] at h
    have h2 : enter_queue e s = [] := by simp_all
    unfold enter_queue at h2
    cases' s with s
    · tauto
    · simp at h2
      ext x
      rw [← PhiNewList_mem]
      simp [h2]

lemma Wenum_infinite_iff (e : ℕ) : (W e).Infinite ↔ ∀ s, ∃ t > s, ∃ n, Wenum e t = some n := by
  have h := Wenum_finite_iff e
  have h1 : ¬ (W e).Finite ↔ (W e).Infinite := by exact Iff.symm (Eq.to_iff rfl)
  simp_all [Option.ne_none_iff_exists']


theorem We_finite_TFAE (e : ℕ) :
  [
    (W e).Finite,
    ∃ s, ∀ t > s, PhiNewList e t = [],
    ∃ s, ∀ t > s, W_s e t = W_s e s,
    ∃ s, W e = W_s e s,
    ∃ s, ∀ t > s, enter_queue e t = [],
    ∃ s, ∀ t > s, Wenum e t = Option.none
  ].TFAE := by
  sorry
