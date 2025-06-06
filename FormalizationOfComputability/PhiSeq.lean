/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.Phi
import Mathlib.Data.WSeq.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Lattice

/-
# Wₑ as a sequence
This file builds W_seq, which enumerates the elements n of W_e
in the order in which ϕ_e(n) halts
-/

namespace Computability

open Nat
open Nat.Partrec
open Nat.Partrec.Code

/- The elements whose computations first halt at stage s, in increasing order.
 Note they are not in W_s! -/
def PhiNewList (e s : ℕ) : List ℕ :=
  (List.range (s+1)).filter (λ n => (Phi_s_halts e (s+1) n ∧ ¬ Phi_s_halts e s n))

def PhiNew (e s : ℕ) : Finset ℕ := (PhiNewList e s).toFinset

/- The elements halting at stage s are exactly W_{e, s+1} \ W_{e, s} -/
lemma PhiNew_eq_Ws_diff (e s : ℕ) : (PhiNew e s) = (W_s e (s+1)) \ (W_s e s) := by
  simp [PhiNew, W_s]
  apply subset_antisymm
  · intro x
    simp
    intro h
    simp [PhiNewList] at h
    constructor
    · constructor
      · exact h.left
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
lemma PhiNew_disjoint_gt (e s t : ℕ) (h : s>t) :
    Disjoint (PhiNew e s) (PhiNew e t) := by
  rw [Finset.disjoint_iff_ne]
  simp [PhiNew, PhiNewList]
  intro a h1 h2 h3 b h4 h5 h6
  contrapose h5
  simp at h5
  rw [h5] at h3
  apply phi_halts_mono_reverse e
  · exact h
  · exact h3

lemma PhiNew_pairwise_disjoint (e : ℕ) :
  Set.PairwiseDisjoint (Set.univ : Set ℕ) (PhiNew e) := by
  intro s _ t _ h
  rw [ne_iff_lt_or_gt] at h
  rcases h with h | h
  · exact Disjoint.symm (PhiNew_disjoint_gt e t s h)
  · exact PhiNew_disjoint_gt e s t h

/- If x is new at stage s, it is not in W_s (elements entering *before* s)-/
lemma PhiNew_is_new (e s : ℕ) : (PhiNew e s) ∩ (W_s e s) = ∅ := by
  rw [PhiNew_eq_Ws_diff]
  simp

/- W_{e, s+1} is exactly W_{e, s} and the new elements at stage s.
Sometimes useful to work with W_{e,s} instead of W_{e, s+1} -/
lemma Ws_plus_one_eq (e s : ℕ) : W_s e (s+1) = (W_s e s) ∪ (PhiNew e s) := by
    rw [PhiNew_eq_Ws_diff]
    simp
    apply W_s_mono e s (s+1)
    simp

lemma Ws_eq (e s : ℕ) (h : s > 0) : W_s e s = (W_s e (s-1)) ∪ (PhiNew e (s-1)) := by
    have h1 : s - 1 + 1 = s := by exact Nat.sub_add_cancel h
    rw [PhiNew_eq_Ws_diff, h1]
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
      apply phi_halts_mono_reverse
      · exact h1
      · exact h.right.right
  · intro h
    rw [runtime_is_min] at h
    rw [PhiNew_eq_Ws_diff]
    simp [W_s]
    have h1 : x < r + 1 := by
      apply halt_input_bound
      exact h.left
    constructor
    · constructor
      · exact h1
      · exact h.left
    · intro h2
      apply Nat.ne_zero_of_lt at h2
      have h3 : r - 1 + 1 = r := by exact succ_pred_eq_of_ne_zero h2
      rw [← Phi_s_diverges]
      rw [← h3]
      apply h.right
      exact Nat.sub_one_lt h2

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
    use s+1
    simp at h
    exact h.left

/- If eventually no new elements ever enter, then W_{e, s} never again changes-/
lemma WsNew_stabilizes_Ws_stabilizes (e t : ℕ) (h : ∀ s ≥ t, PhiNew e s = ∅) :
    ∀ s ≥ t, W_s e s = W_s e t := by
  have h1 : ∀ s ≥ t, (W_s e (s+1)) = (W_s e s) := by
    intro s h2
    apply h at h2
    simp [Ws_plus_one_eq, h2]
  intro s h3
  induction' s using Nat.strong_induction_on with s ih
  by_cases h4 : s = t
  · simp [h4]
  · have h5 : s-1 ≥ t := by
      refine le_sub_one_of_lt ?_
      exact Nat.lt_of_le_of_ne h3 fun a ↦ h4 (id (Eq.symm a))
    have h6 : (W_s e (s-1)) = (W_s e t) := by
      apply ih (s-1)
      · apply Nat.sub_one_lt
        cases t
        · tauto
        · linarith
      exact h5
    rw [← h6]
    have h7 : W_s e ((s - 1) + 1) = (W_s e (s-1)) := by
      exact h1 (s - 1) h5
    have h8 : s - 1 + 1 = s := by
      refine Nat.sub_add_cancel ?_
      cases t
      · exact one_le_iff_ne_zero.mpr h4
      · exact one_le_of_lt h3
    rw [h8] at h7
    exact h7

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

/- W_e is finite iff eventually there are no new elements-/
lemma PhiNew_stabilizes_implies_We_finite (e t : ℕ) (h : ∀ s ≥ t, PhiNew e s = ∅) :
    (W e).Finite := by
  rw [We_eq_union_WsNew, Set.finite_iUnion_iff]
  · simp
    apply Set.Finite.subset (Set.finite_lt_nat t)
    simp
    intro s h1
    contrapose h1
    simp at h1
    apply h at h1
    rw [h1]
    simp
  · simp
    intro i j h1
    apply PhiNew_pairwise_disjoint
    simp
    simp
    simp
    exact h1

lemma PhiNew_stabilizes_implies_We_eq_Ws (e t : ℕ) (h : ∀ s ≥ t, PhiNew e s = ∅) :
    W e = W_s e t := by
  rw [We_eq_union_WsNew]
  apply subset_antisymm
  · intro x h1
    simp at h1
    obtain ⟨i, h1⟩ := h1
    have h2 : i < t := by
      contrapose h1
      simp at h1
      apply h at h1
      rw [h1]
      simp
    have h3 : x ∈ W_s e (i+1) := by
      rw [Ws_plus_one_eq]
      simp
      right
      exact h1
    apply W_s_mono e (i+1)
    · exact h2
    · exact h3
  · intro x h1
    apply Ws_runtime at h1
    obtain ⟨r, ⟨h1, h2⟩⟩ := h1
    rw [← PhiNew_runtime_iff] at h1
    simp
    use r

lemma We_finite_implies_Ws_stabilizes (e : ℕ) (h : (W e).Finite) :
    ∃ t, ∀ s ≥ t, PhiNew e s = ∅ := by
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
      use N+1
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

-- lemma We_finite_implies_We_eq_Ws

lemma We_finite_iff_Ws_stabilizes (e : ℕ) :
    (W e).Finite ↔ (∃ t, ∀ s ≥ t, PhiNew e s = ∅) := by
  constructor
  · apply We_finite_implies_Ws_stabilizes e
  · intro ⟨t, h⟩
    apply PhiNew_stabilizes_implies_We_finite
    exact h

-- We_eq_Ws_iff_Ws_stabilizes


/- x appears as a new element at its runtime -/
lemma PhiNew_runtime (y e s : ℕ) : y ∈ PhiNew e s ↔ s ∈ runtime e y := by
  simp [runtime, rfindOpt]
  constructor
  · simp [PhiNew, PhiNewList, W_s]
    intro h1 h2 h3
    constructor
    · constructor
      · exact Option.isSome_iff_exists.mpr h2
      · have h4 : Phi_s_halts e s y → y < s := by
          apply halt_input_bound
        intro m hm
        apply phi_halts_mono_reverse e (m+1) at h3
        · unfold Phi_s_diverges Phi_s_halts at h3
          push_neg at h3
          exact Option.eq_none_iff_forall_ne_some.mpr h3
        · exact hm
    exact Option.isSome_iff_exists.mpr h2
  · intro ⟨⟨h, h1⟩, h2⟩
    clear h2
    apply Option.isSome_iff_exists.mp at h
    simp [PhiNew, PhiNewList]
    constructor
    · apply halt_input_bound e
      unfold Phi_s_halts
      exact h
    · constructor
      · exact h
      · unfold Phi_s_halts
        push_neg
        intro y
        by_cases h2 : s=0
        · simp [h2]
          unfold Phi_s
          simp
        · have h3 : s - 1 < s := by
            exact sub_one_lt h2
          apply h1 at h3
          rw [sub_one_add_one_eq_of_pos] at h3
          · rw [Option.eq_none_iff_forall_not_mem] at h3
            exact h3 y
          · exact zero_lt_of_ne_zero h2

/- The elements in W_e enumerated before stage s, in the order they appeared -/
def W_prefix (e : ℕ) : ℕ → List ℕ
| 0     => []
| s + 1 => (W_prefix e s) ++ (PhiNewList e s)

-- flatten PhiNewList e t from t=0 to t=s

open List.Nodup

lemma W_s_eq_prefix (e s : ℕ) : W_s e s = (W_prefix e s).toFinset := by
  induction' s with s hs
  · simp [W_prefix, W_s]
  · apply subset_antisymm
    intro y h
    simp [W_prefix]
    by_cases h1 : y ∈ (W_s e s)
    · left
      rw [← List.mem_toFinset, ← hs]
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
      simp [W_prefix, PhiNew, W_s, ← List.mem_toFinset, ← hs] at h
      simp [W_s]
      simp [W_s] at h
      rcases h with h | h
      · constructor
        · linarith
        · refine phi_halts_mono e s (s + 1) x (le_add_right s 1) h.right
      · tauto

lemma nodup_W_prefix (e s : ℕ) : List.Nodup (W_prefix e s) := by
  induction' s with s ih
  · unfold W_prefix
    simp
  · simp [W_prefix]
    apply append
    · exact ih
    · apply List.Nodup.filter
      exact List.nodup_range
    · unfold List.Disjoint
      intro a h h1
      rw [← List.mem_toFinset, PhiNew_eq] at h1
      rw [← List.mem_toFinset, ← W_s_eq_prefix] at h
      simp at h1
      obtain ⟨h1, h2⟩ := h1
      contradiction

lemma W_prefix_mono (e s t : ℕ) (h : s ≤ t) :
  (W_prefix e s) <+: (W_prefix e t) := by
  induction' t with t ih
  · simp at h
    rw [h]
  · by_cases h1 : s = t + 1
    · rw [h1]
    · have h2 : s ≤ t := by
        exact le_of_lt_succ (lt_of_le_of_ne h h1)
      apply ih at h2
      apply List.IsPrefix.trans h2
      simp [W_prefix]

open Stream'
open Stream'.Seq

-- due to Mario Carneiro
def prefix_union_step : (ℕ → List ℕ) → WSeq ℕ :=
  Seq.corec fun f =>
    match f 0 with
    | [] => some (Option.none, fun n => f (n+1))
    | .cons a _ => some (some a, fun n => (f n).tail)

/- This tracks what happens at each stage, emitting 'none' when no elements halt-/
def W_seq_step (e : ℕ) : WSeq ℕ := prefix_union_step (W_prefix e)

partial def W_stream (e : ℕ) (s : ℕ) (prev : List ℕ) : Stream' (Option ℕ) :=
  let diff := (W_prefix e s).drop prev.length
  match diff with
  | [] =>
    W_stream e (s + 1) prev
  | List.cons h _ =>
    Stream'.cons (some h) (W_stream e s (prev ++ [h]))

lemma W_stream_finite (e : ℕ) : (W e).Finite → (∃ N, ∀ n ≥ N, ¬(W_stream e)[n]?) := by
  constructor

def W_seq_stream (e : ℕ) : Stream'.Seq ℕ :=
  let init := W_prefix e 0
  ⟨W_stream e 1 init, by
    unfold IsSeq
    intro n h
    by_cases h1 : (W e).Finite
    ·
    ·
  ⟩

/- W_seq skips 'none' when there is a next element-/
partial def W_seq (e : ℕ) : WSeq ℕ :=
  Seq.corec (fun (state : ℕ × List ℕ) =>
    let (s, remaining) := state
    match remaining with
    | []   =>
      let new := PhiNew e s
      match new with
      | []      => Option.none  -- diverge if no new element at this stage
      | .cons a tail! => some (a, (s + 1, tail!))
    | .cons a tail! => some (a, (s, tail!))
  ) (0, [])

lemma W_prefix_true (e s n : ℕ) :
  n ∈ (W_prefix e s) ↔ n ∈ W_seq_stream e := by
  rw [splitAt.eq_def]
  ext i a
  simp only [List.get_ofFn]
  induction' h : (W_prefix e s).length with n ih generalizing i
  · have h1 : (W_prefix e s) = [] := by exact List.eq_nil_iff_length_eq_zero.mpr h
    simp [h1]
  · by_cases h2 : i ≤ n

-- the below was all built when W_seq was a Stream', not a WSeq.

lemma W_seq_aux_lemma (e k s n: ℕ) (acc : List ℕ) (h : W_seq.aux e k s acc = n):
    ∃ t, n ∈ W_prefix e t := by
  sorry

lemma exists_stage_of_mem {e n : ℕ} (h : n ∈ Set.range (W_seq e)) :
    ∃ s, n ∈ W_prefix e s := by
  rcases h with ⟨k, hk⟩
  suffices aux : ∀ (k : ℕ), W_seq e k = n → ∃ s, n ∈ W_prefix e s by
      exact aux k hk
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro h
    unfold W_seq at h
    exact W_seq_aux_lemma e l 0 n [] h


lemma W_seq_mem_iff (e n : ℕ) : n ∈ Set.range (W_seq e) ↔ ∃ t, n ∈ W_prefix e t := by
  constructor
  · intro h
    apply exists_stage_of_mem at h
    exact h
  · intro h
    obtain ⟨s, h⟩ := h


lemma mem_W_seq_iff_halt (e n : ℕ) : n ∈ Set.range (W_seq e) ↔ Phi_halts e n := by
  constructor
  · intro h
    rw [W_seq_mem_iff] at h
    obtain ⟨t, h⟩ := h
    refine (phi_halts_stage_exists e n).mpr ?_
    have h1 : ∃ s, n ∈ W_s e s := by
      use t
      simp [W_s_eq_prefix]
      exact h
    obtain ⟨s, h1⟩ := h1
    use s
    exact (W_s_Phi_s e s n).mp h1
  · intro h
    rw [phi_halts_stage_exists] at h
    obtain ⟨s, h⟩ := h
    rw [W_seq_mem_iff]
    use s
    have h1 : n ∈ W_s e s := by
      exact (W_s_Phi_s e s n).mpr h
    rw [W_s_eq_prefix] at h1
    exact List.mem_dedup.mp h1

theorem W_enum_eq_W (e : ℕ) : W e = Set.range (W_seq e) := by
  ext n
  rw [mem_W_phi, ← mem_W_seq_iff_halt]


lemma inf_inc_sigma01_seq_is_delta01 (e : ℕ) (h1 : (W e).Infinite)
    (h2 : ∀ (n : ℕ), W_seq e n < W_seq e (n+1)) :
    Delta01 (W e) := by
sorry

-- for any given x, ∃ n x < W_enum n (lest W e not be increasing and infinite)
-- if ∃ m < n x = W_enum m, then x ∈ W e
-- else x ∉ W e
-- bounded quantifiers are decidable

/- lemma sigma01_has_delta01_subset (X : Set ℕ) (hX : Sigma01 X) (hInf : X.Infinite):
∃ (Y : Set ℕ), Delta01 Y ∧ Y.Infinite ∧ Y ⊆ X ∧ (X\Y).Infinite := by
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
