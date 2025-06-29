/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.Phi
import Mathlib.Data.WSeq.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Card

/- # Wₑ as a sequence
This file builds W_seq, which enumerates the elements n of W_e in the order that each ϕ_e(n) halts -/

namespace Computability

open Nat
open Nat.Partrec
open Nat.Partrec.Code
open List

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

/-- The elements newly halting at stage s are exactly W_{e, s} \ W_{e, s-1} -/
lemma PhiNew_eq_Ws_diff (e s : ℕ) : (PhiNew e s) = (W_s e s) \ (W_s e (s-1)) := by
  simp [PhiNew, W_s]
  apply subset_antisymm
  · intro x
    simp
    intro h
    simp [PhiNewList] at h
    constructor
    · constructor
      · linarith
      · apply phi_halts_mono e s
        · linarith
        · exact h.right.left
    · intro h1
      exact h.right.right
  · intro x
    simp
    intro h1 h2 h3
    simp [PhiNewList]
    constructor
    · exact h1
    · constructor
      · exact h2
      · contrapose h3
        simp
        simp at h3
        constructor
        · apply halt_input_bound
          exact h3
        · exact h3

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
  · intro h
    rw [runtime_is_min]
    simp [PhiNew, PhiNewList] at h
    constructor
    · exact h.right.left
    · intro t h1
      apply phi_halts_mono_reverse e t (r-1)
      · exact le_sub_one_of_lt h1
      · exact h.right.right
  · intro h
    rw [runtime_is_min] at h
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


/- TFAE :
Eventually all PhiNew e s = ∅
W_e is finite
There is an s such that W_e = W_{e, s}
-/

lemma PhiNew_stabilizes_implies_We_finite (e s : ℕ) (h : ∀ t > s, PhiNew e t = ∅) :
    (W e).Finite := by
  rw [We_eq_union_WsNew, Set.finite_iUnion_iff]
  · simp
    apply Set.Finite.subset (Set.finite_le_nat s)
    simp
    intro t h1
    contrapose h1
    simp at h1
    simp [h, h1]
  · simp
    intro i j h1
    apply PhiNew_pairwise_disjoint
    · simp
    · simp
    · simp
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
    simp
    simp
    simp
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

open List.Nodup

/- Elements cannot be enumerated twice-/
lemma nodup_WPrefix (e s : ℕ) : Nodup (WPrefix e s) := by
  induction' s with s ih
  · unfold WPrefix
    simp
  · simp [WPrefix]
    apply append
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

theorem idxOf?_mem {α : Type} [inst : DecidableEq α] {a : α} {n : ℕ} {L : List α}
    (h : n = List.idxOf? a L) : L[n]? = a := by
  have := List.of_findIdx?_eq_some h.symm
  generalize hi : L[n]? = i at this ⊢
  cases i <;> simp_all

theorem mem_idxOf? {α : Type} [inst : DecidableEq α] {a : α} {n : ℕ} {L : List α}
    (h : List.Nodup L) (h1 : L[n]? = a) : n = List.idxOf? a L := by
  have h2 : n < L.length := by
    exact (isSome_getElem? L n).mp (Option.isSome_of_mem h1)
  have h3 : L[n] = a := by
    exact (List.getElem_eq_iff h2).mpr h1
  rw [List.idxOf?, eq_comm, List.findIdx?_eq_some_iff_findIdx_eq, List.findIdx_eq]
  constructor
  · exact h2
  · constructor
    · simp [h3]
    · intro j hjn
      simp [← h3]
      rw [List.Nodup.getElem_inj_iff]
      · apply Nat.ne_of_lt hjn
      · exact h
  · exact h2

/- It is often useful to view elements entering one at a time, so there may be a queue
of elements waiting to enter. This represents the elements still waiting *at* stage s,
i.e. the head of this list will be enumerated at stage s. -/
def enter_queue (e : ℕ) : ℕ → List ℕ
  | 0 => []
  | s + 1 => (enter_queue e s).tail ++ (PhiNewList e (s+1))

/- If n is in an queue at stage s, then ϕ_{e, s}(n)↓ -/
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

/- Elements of the queues are exactly the elements that halt -/
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

/- If n is not the head of an queue, then at the next step its index decreases by 1. -/
lemma enter_queue_dec (e n s : ℕ)
    (h : n ∈ (enter_queue e s).tail) :
    List.idxOf n (enter_queue e (s+1)) = List.idxOf n (enter_queue e s) - 1 := by
  dsimp [enter_queue]
  simp [List.idxOf_append, h]
  cases' L : enter_queue e s with a T
  · tauto
  · simp [L] at h
    apply Nat.eq_sub_of_add_eq
    apply Eq.symm (List.idxOf_cons_ne T ?_)
    have h2 := enter_queue_nodup e s
    rw [L] at h2
    apply List.Nodup.notMem at h2
    exact Ne.symm (ne_of_mem_of_not_mem h h2)

/- If PhiNew stabilizes, then eventually the queue depletes. Indeed iff is true,
but not proved here. -/

lemma queue_depletes (e s : ℕ) (h : ∀ t > s, PhiNew e t = ∅) :
    ∃ s₁, ∀ t > s₁, enter_queue e t = [] := by
  sorry
  /- let l := (enter_queue e t).length
    use t+l-1
    intro s h1
    simp [Wenum, new_element]
    unfold enter_queue
    have h2 := enter_queue_WPrefix e s
    sorry -- can't use t - there may be a queue to be emptied -/

/- The element that has been emitted at stage s, if it exists -/
def new_element (e s : ℕ) : Option ℕ := (enter_queue e s).head?

def Wenum (e : ℕ) : Stream' (Option ℕ) := new_element e

lemma Wenum_finite_iff (e : ℕ) : (W e).Finite ↔ ∃ s, ∀ t > s, Wenum e t = Option.none := by
  rw [We_finite_iff_PhiNew_stabilizes]
  constructor
  · intro ⟨s, h⟩
    have ⟨s₁, h1⟩ := queue_depletes e s h
    use s₁
    intro t ht
    simp [Wenum, new_element]
    apply h1
    exact ht
  · intro ⟨t, h⟩
    use t
    intro s h1
    simp [Wenum, new_element] at h
    have h2 : enter_queue e s = [] := by
      apply h
      linarith
    unfold enter_queue at h2
    cases' s with s
    · tauto
    · simp at h2
      ext x
      rw [← PhiNewList_mem]
      simp [h2]


lemma Phi_halts_new_element (e n : ℕ) : Phi_halts e n ↔ ∃ s, new_element e s = n := by
  simp [new_element]
  rw [← enter_queue_mem]
  constructor
  · intro ⟨s, h⟩
    have h1 : ∃ k, k = (enter_queue e s).findIdx (· = n) := by
      exact exists_apply_eq_apply (fun a ↦ a) (idxOf n (enter_queue e s))
    obtain ⟨k, h1⟩ := h1
    use s+k
    induction' k with k' ih
    · sorry
    · sorry
  · intro ⟨s, h⟩
    use s
    exact List.mem_of_mem_head? h






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









lemma inf_inc_sigma01_seq_is_delta01 (e : ℕ) (h1 : (W e).Infinite)
    (h2 : ∀ (n : ℕ), W_seq e n < W_seq e (n+1)) :
    Delta01 (W e) := by
  sorry

-- for any given x, ∃ n x < W_enum n (lest W e not be increasing and infinite)
-- if ∃ m < n x = W_enum m, then x ∈ W e
-- else x ∉ W e
-- bounded quantifiers are decidable

/- lemma sigma01_has_delta01_subset (X : Set ℕ) (hX : Sigma01 X) (hInf : X.Infinite):
∃ (Y : Set ℕ), Delta01 Y ∧ Y.Infinite ∧ Y ⊆ X := by
obtain ⟨f, ⟨hfPart, hfDom⟩⟩ := hX
let g := f.map (fun _ => 1)
have hfg : ∀ (x:ℕ), (f x) = some () ↔ (g x) = 1 := by
  sorry
have hgPart : Nat.Partrec g := by
  sorry
rw [Nat.Partrec.Code.exists_code] at hgPart
obtain ⟨e, he⟩ := hgPart
sorry -/

-- Views Of Mount Σ01 :
-- partial recursive f
-- its domain X
-- the range of a computable g : ℕ → ℕ
-- the code e for f
-- the (possibly finite) sequence of nth outputs {fn}
-- the infinite partial recursive sequence of nth outputs {fn}
