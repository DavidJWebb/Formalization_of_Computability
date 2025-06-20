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
This file builds W_seq, which enumerates the elements n of W_e
in the order in which ϕ_e(n) halts -/

namespace Computability

open Nat
open Nat.Partrec
open Nat.Partrec.Code

/- The elements whose computations first halt at stage s, in increasing order. By definition,
these elements are less than s. -/
def PhiNewList (e s : ℕ) : List ℕ :=
  (List.range s).filter (λ n => (Phi_s_halts e s n ∧ ¬ Phi_s_halts e (s-1) n))

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

/- W_{e, s+1} is exactly W_{e, s} and the new elements at stage s+1. -/
lemma Ws_plus_one_eq (e s : ℕ) : W_s e (s+1) = (W_s e s) ∪ (PhiNew e (s+1)) := by
    rw [PhiNew_eq_Ws_diff]
    simp
    apply W_s_mono e s (s+1)
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
W_e is finite
W_e = some W_{e, s}
Eventually there are no new elements -/
lemma PhiNew_stabilizes_implies_We_finite (e t : ℕ) (h : ∀ s > t, PhiNew e s = ∅) :
    (W e).Finite := by
  rw [We_eq_union_WsNew, Set.finite_iUnion_iff]
  · simp
    apply Set.Finite.subset (Set.finite_le_nat t)
    simp
    intro s h1
    contrapose h1
    simp at h1
    simp [h, h1]
  · simp
    intro i j h1
    apply PhiNew_pairwise_disjoint
    simp
    simp
    simp
    exact h1

lemma PhiNew_stabilizes_implies_We_eq_Ws (e t : ℕ) (h : ∀ s > t, PhiNew e s = ∅) :
    W e = W_s e t := by
  rw [We_eq_union_WsNew]
  apply subset_antisymm
  · intro x h1
    simp at h1
    obtain ⟨r, h1⟩ := h1
    have h2 : r ≤ t := by
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

lemma We_finite_implies_Ws_stabilizes (e : ℕ) (h : (W e).Finite) :
    ∃ t, ∀ s > t, PhiNew e s = ∅ := by
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

lemma We_finite_iff_Ws_stabilizes (e : ℕ) :
    (W e).Finite ↔ (∃ t, ∀ s > t, PhiNew e s = ∅) := by
  constructor
  · apply We_finite_implies_Ws_stabilizes e
  · intro ⟨t, h⟩
    apply PhiNew_stabilizes_implies_We_finite
    exact h

lemma We_finite_iff_We_eq_Ws (e : ℕ) : (W e).Finite ↔ ∃ s, W e = W_s e s := by
  constructor
  · rw [We_finite_iff_Ws_stabilizes]
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
    · constructor
      · exact Option.isSome_iff_exists.mpr h1
      · intro m hm
        have h3 : Phi_s_halts e s y → y < s := by
          apply halt_input_bound
        apply phi_halts_mono_reverse e m at h2
        · unfold Phi_s_diverges Phi_s_halts at h2
          push_neg at h2
          exact Option.eq_none_iff_forall_ne_some.mpr h2
        · exact le_sub_one_of_lt hm
    exact Option.isSome_iff_exists.mpr h1
  · intro ⟨⟨h, h1⟩, h2⟩
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
          simp [h3]

/- The elements in W_e enumerated up to stage s, in the order they appeared -/
def WPrefix (e : ℕ) : ℕ → List ℕ
| 0     => []
| s + 1 => (WPrefix e s) ++ (PhiNewList e (s+1))

-- flatten PhiNewList e t from t=0 to t=s?

open List.Nodup

/- WPrefix e s is exactly W_{e, s} in order of enumeration -/
lemma Ws_eq_prefix (e s : ℕ) : W_s e s = (WPrefix e s).toFinset := by
  induction' s with s hs
  · simp [WPrefix, W_s]
  · apply subset_antisymm
    intro y h
    simp [WPrefix]
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
      simp [WPrefix, PhiNew, W_s] at h
      rw [PhiNewList_mem, ← List.mem_toFinset, ← hs] at h
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
  rw [← List.mem_toFinset, Ws_eq_prefix]

/- Elements cannot be enumerated twice-/
lemma nodup_WPrefix (e s : ℕ) : List.Nodup (WPrefix e s) := by
  induction' s with s ih
  · unfold WPrefix
    simp
  · simp [WPrefix]
    apply append
    · exact ih
    · apply List.Nodup.filter
      exact List.nodup_range
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


/- The first n elements of W_e, in enumeration order (if it has that many)-/
/- partial def WnUpToAux (e n s : ℕ) (acc : List ℕ) : Option (List ℕ) :=
  if acc.length ≥ n then
    some acc
  else
    WnUpToAux e n (s + 1) (acc ++ ((WPrefix e s).filter (· ∉ acc)))

def WnUpTo (e n : ℕ) : Option (List ℕ) :=
  WnUpToAux e n 0 [] -/

open Stream'
open Stream'.Seq

-- due to Mario Carneiro
def PrefixUnionStage : (ℕ → List ℕ) → WSeq ℕ :=
  Seq.corec fun f =>
    match f 0 with
    | [] => some (Option.none, fun n => f (n+1))
    | .cons a _ => some (some a, fun n => (f n).tail)

/- This tracks what happens at each stage, emitting 'none' when no elements halt-/
def Wenum (e : ℕ) : WSeq ℕ := PrefixUnionStage (WPrefix e)


lemma Wenum_mem (e n x: ℕ) (h : WSeq.get? (Wenum e) n = some x) : ∃ s, x ∈ WPrefix e s := by
  simp [Wenum, PrefixUnionStage] at h
  induction' n with n ih
  · simp [WSeq.get?] at h
    cases' WPrefix e 0 with a tail!


  · sorry

/- def WEnum (e : ℕ) : Stream'.Seq ℕ :=
  ⟨WStream e 1 [], by sorry
  ⟩ -/







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
