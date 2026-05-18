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


/- The elements whose computations first halt at stage s. By definition,
these elements are less than s. -/
def ϕNew (e s : ℕ) : Finset ℕ := (W_s e s).filter (λ n ↦ ϕ_s e (s-1) n = Option.none)

instance ϕNew_dec (e s n : ℕ) : Decidable (n ∈ ϕNew e s) := by
  exact Finset.decidableMem n (ϕNew e s)

lemma ϕNew_zero (e : ℕ) : ϕNew e 0 = ∅ := by simp [ϕNew]

variable {e s t n x y i k l : ℕ}

/- This lemma cleans up lines that would otherwise be a rather lengthy simp only -/
lemma ϕNew_mem : x ∈ ϕNew e s ↔ (x < s ∧ ϕ_s_halts e s x ∧ ¬ϕ_s_halts e (s - 1) x) := by
  simp [ϕNew, ϕ_s_halts]
  intro h h1
  exact ϕ_input_bound h

/- The elements newly halting at stage s are exactly W_{e, s} \ W_{e, s-1} -/
@[grind =]
lemma ϕNew_eq_Ws_diff : (ϕNew e s) = (W_s e s) \ (W_s e (s-1)) := by
  apply subset_antisymm
  · intro x
    simp_all [ϕNew]
  · intro x
    simp_all only [ϕNew]
    intro h
    simp only [Finset.mem_filter]
    sorry






/- Elements never enter twice - the ϕNew are disjoint -/
lemma ϕNew_disjoint_gt (h : s > t) : Disjoint (ϕNew e s) (ϕNew e t) := by
  rw [Finset.disjoint_iff_ne]
  intros a ha b hb
  have ⟨d, hd⟩ := Nat.exists_eq_add_of_lt h
  have hb1 : b ∈ W_s e (t+d) := by
    apply (W_s_mono (Nat.le_add_right t d))
    rw [ϕNew_eq_Ws_diff, Finset.mem_sdiff] at hb
    exact hb.left
  grind

lemma ϕNew_pairwise_disjoint (e : ℕ) : Set.PairwiseDisjoint (Set.univ : Set ℕ) (ϕNew e) := by
  intro s _ t _ h
  rw [ne_iff_lt_or_gt] at h
  rcases h with h | h
  · exact Disjoint.symm (ϕNew_disjoint_gt h)
  · exact ϕNew_disjoint_gt h

/- If x is new at stage s, it is not in W_s (elements entering *before* s)-/
lemma ϕNew_is_new (e s : ℕ) : (ϕNew e s) ∩ (W_s e (s-1)) = ∅ := by simp [ϕNew_eq_Ws_diff]

/- It is sometimes useful to work with W_{e,s} instead of W_{e, s+1} -/
lemma Ws_eq (e s : ℕ) : W_s e s = (W_s e (s-1)) ∪ (ϕNew e s) := by
    rw [ϕNew_eq_Ws_diff]
    simp only [Finset.union_sdiff_self_eq_union, Finset.right_eq_union]
    apply W_s_mono
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right, _root_.zero_le]

/- The new elements at stage s are exactly those with runtime s -/
lemma ϕNew_runtime_iff (e x r : ℕ) : x ∈ ϕNew e r ↔ r ∈ runtime e x := by
  simp only [runtime, ϕNew_eq_Ws_diff, Finset.mem_sdiff, Part.coe_some, mem_rfind,
    Part.mem_some_iff, Bool.true_eq, Bool.false_eq, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]
  constructor
  <;> intro ⟨h, h1⟩
  <;> constructor
  · exact W_s_ϕ_s.mp h
  · intro m hm
    contrapose h1
    exact W_s_mono (le_sub_one_of_lt hm) (W_s_ϕ_s.mpr (Option.isSome_iff_ne_none.mpr h1))
  · exact W_s_ϕ_s.mpr h
  · by_cases hr : r = 0
    · simp [hr]
    · have h2 : r-1 < r := by exact Nat.sub_one_lt hr
      apply h1 at h2
      sorry

/- W_e can be created as a disjoint union of new elements-/
lemma We_eq_union_ϕNew (e : ℕ) : W e = ⋃ s, (ϕNew e s) := by
  rw [W_eq_union_W_s]
  apply subset_antisymm
  <;> intro x h
  <;> simp_all only [Set.mem_iUnion, Finset.mem_coe]
  · obtain ⟨_, h⟩ := h
    apply Ws_runtime at h
    obtain ⟨r, h⟩ := h
    simp only [ϕNew_runtime_iff]
    exact ⟨r, h.left⟩
  · grind

/- TFAE :
Eventually all ϕNew e s = ∅
W_e is finite
There is an s such that W_e = W_{e, s}
-/

/- TODO : Move any implications not needed for lemmas to the TFAE -/
lemma ϕNew_stabilizes_implies_We_finite (e s : ℕ) (h : ∀ t > s, ϕNew e t = ∅) :
    (W e).Finite := by
  rw [We_eq_union_ϕNew, Set.finite_iUnion_iff]
  · simp only [Finset.finite_toSet, implies_true, Finset.coe_nonempty, true_and]
    apply Set.Finite.subset (Set.finite_le_nat s)
    grind
  · simp only [Finset.disjoint_coe]
    intro i j h1
    apply ϕNew_pairwise_disjoint
    <;> simp only [Set.mem_univ, ne_eq]
    exact h1

lemma We_finite_implies_ϕNew_stabilizes (e : ℕ) (h : (W e).Finite) :
    ∃ s, ∀ t > s, ϕNew e t = ∅ := by
  rw [We_eq_union_ϕNew, Set.finite_iUnion_iff] at h
  simp only [Finset.finite_toSet, implies_true, Finset.coe_nonempty, true_and] at h
  have h1 := Set.Finite.exists_finset h
  obtain ⟨P, h1⟩ := h1
  · by_cases h2 : P = ∅
    · use 0
      simp_all
    · use Finset.max' P (Finset.nonempty_iff_ne_empty.mpr h2)
      intro s h3
      contrapose h3
      simp only [gt_iff_lt, Finset.max'_lt_iff, not_forall, not_lt]
      use s
      grind
  · simp only [Finset.disjoint_coe]
    intro i j h1
    apply ϕNew_pairwise_disjoint
    <;> simp only [Set.mem_univ, ne_eq]
    exact h1

lemma We_finite_iff_ϕNew_stabilizes (e : ℕ) :
    (W e).Finite ↔ (∃ t, ∀ s > t, ϕNew e s = ∅) := by
  constructor
  · exact We_finite_implies_ϕNew_stabilizes e
  · intro ⟨_, h⟩
    exact ϕNew_stabilizes_implies_We_finite _ _ h

def ϕNewList (e s : ℕ):= (ϕNew e s).sort

instance ϕNewList_dec (e s n : ℕ) : Decidable (n ∈ ϕNewList e s) := by
  simp_rw [← mem_toFinset]
  apply Finset.decidableMem

/- The elements in W_e enumerated up to stage s, in the order they appeared. Elements halting
at the same time are enumerated in asceding order. -/
def WPrefix (e : ℕ) : ℕ → List ℕ
    | 0     => []
    | s + 1 => (WPrefix e s) ++ ϕNewList e (s+1)

/- WPrefix e s is exactly W_{e, s} in order of enumeration -/
lemma Ws_eq_prefix (e s : ℕ) : W_s e s = (WPrefix e s).toFinset := by
  induction s with | zero | succ s hs
  · exact Finset.val_inj.mp rfl
  · rw [Ws_eq]
    unfold WPrefix ϕNewList
    simp_all only [W_s, add_tsub_cancel_right, toFinset_append, Finset.sort_toFinset]

instance WPrefix_dec (e s n : ℕ) : Decidable (n ∈ WPrefix e s) := by
  simp_rw [← mem_toFinset]
  apply Finset.decidableMem

/- Elements cannot be enumerated twice-/
lemma nodup_WPrefix (e s : ℕ) : Nodup (WPrefix e s) := by
  induction s with | zero | succ s ih
  · simp [WPrefix]
  · simp only [WPrefix, ϕNewList]
    apply List.Nodup.append ih
    · simp only [Finset.sort_nodup]
    · rw [ϕNew_eq_Ws_diff]
      simp only [add_tsub_cancel_right]
      refine disjoint_left.mpr ?_
      intro a ha
      simp only [Finset.mem_sort, Finset.mem_sdiff, not_and]
      intro hb
      simp_all only [Ws_eq_prefix, mem_toFinset, not_not]

/- The WPrefixes are prefixes of each other-/
lemma WPrefix_mono (e s t : ℕ) (h : s ≤ t) :
  (WPrefix e s) <+: (WPrefix e t) := by
  induction t with | zero | succ t ih
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
  | s + 1 => (enter_queue e s).tail ++ (ϕNew e (s+1)).sort

instance enter_queue_dec (e s n : ℕ) : Decidable (n ∈ enter_queue e s) := by
  simp_rw [← mem_toFinset]
  apply Finset.decidableMem

instance enter_queue_comp (e : ℕ) : Computable (enter_queue e) := by
  unfold Computable
  sorry


/- If n is in the queue at stage s, then ϕ_{e, s}(n)↓ -/
lemma enter_queue_halts (h : n ∈ enter_queue e s) : ϕ_s_halts e s n := by
  induction s with | zero | succ s ih
  · tauto
  · simp only [enter_queue, List.mem_append] at h
    cases h with | inl h | inr h
    · apply List.mem_of_mem_tail at h
      apply ih at h
      exact ϕ_halts_mono (Nat.le_add_right s 1) h
    · simp_all only [ϕ_s_halts, Finset.mem_sort, ϕNew_mem, add_tsub_cancel_right,
      Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

/- Elements of the queue are exactly the elements that halt -/
lemma enter_queue_mem (e n : ℕ) : (∃ s, n ∈ enter_queue e s) ↔ ϕ_halts e n := by
  constructor
  · intro ⟨s, h⟩
    apply enter_queue_halts at h
    apply (ϕ_complete).mpr
    use s
  · intro h
    simp only [ϕ_halts_runtime_exists, ← ϕNew_runtime_iff] at h
    obtain ⟨r, h⟩ := h
    use r
    unfold enter_queue
    cases r with | zero | succ r
    · tauto
    · simp only [mem_append]
      right
      simp [h]

/- A lemma for moving from (enter_queue e s) to (enter_queue e t) -/
lemma enter_queue_ϕNewList (e : ℕ) (h : s ≥ t) :
    (enter_queue e s) ⊆
    (enter_queue e t) ++ flatten ((range (s - t)).map (λ i ↦ ϕNewList e (t + i + 1))) := by
  apply Nat.exists_eq_add_of_le at h
  obtain ⟨k, h⟩ := h
  revert s
  induction k with | zero | succ k ih
  · simp_all
  · simp_all only [add_tsub_cancel_left, forall_eq]
    intro x xh
    simp [enter_queue] at xh
    cases xh with | inl xh | inr xh
    · apply mem_of_mem_tail at xh
      apply ih at xh
      simp_all
      cases xh with | inl xh | inr xh
      · exact Or.inl xh
      · apply Or.inr
        obtain ⟨a, xh⟩ := xh
        use a
        exact ⟨Nat.lt_add_right 1 xh.left, xh.right⟩
    · refine mem_append_right (enter_queue e t) ?_
      refine mem_flatten.mpr ?_
      simp
      use k
      simp [ϕNewList, xh]

/- The queue at stage s is a suffix of WPrefix e s.
This is mostly here so that it's easy to show that enter queues have no duplicates -/
lemma enter_queue_WPrefix (e s : ℕ) :
    IsSuffix (enter_queue e s) (WPrefix e s) := by
  induction s with | zero | succ s ih
  · simp [enter_queue]
  · unfold enter_queue WPrefix
    have h1 := List.IsSuffix.trans (tail_suffix (enter_queue e s)) ih
    cases L : (enter_queue e s) with | nil | cons a T
    · exact suffix_append (WPrefix e s) ((ϕNew e (s + 1)).sort fun a b ↦ a ≤ b)
    · simp [IsSuffix, L, tail_cons] at h1
      obtain ⟨S, h1⟩ := h1
      use S
      simp [← h1]
      exact toList_toArray

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
  · grind
  · have ⟨_, h⟩ := enter_queue_WPrefix e s
    have h1 := nodup_WPrefix e s
    rw [← h] at h1
    exact List.Nodup.of_append_right h1

/- If n is not the head of an queue, then at the next step its index decreases by 1. -/
lemma enter_queue_dec_stage (h : n ∈ (enter_queue e s).tail) :
     List.idxOf? n (enter_queue e (s + 1)) = (List.idxOf? n (enter_queue e s)).map (· - 1) := by
  simp only [enter_queue, idxOf?_append, h, ↓reduceIte]
  cases hL : enter_queue e s with | nil | cons a T
  · tauto
  · simp only [tail_cons]
    rw [index_tail] at h
    obtain ⟨k, ⟨h, h1⟩⟩ := h
    rw [← idxOf?_getElem?_iff] at h1
    · simp_all only [ge_iff_le]
      have h3 : some k = idxOf? n ([a] ++ T) := by exact h1
      rw [List.idxOf?_append] at h3
      have h4 : n ∈ (a :: T).tail := by
        apply idxOf?_getElem? at h1
        apply index_tail.mpr
        use k
      have h5 : n ≠ a := by
        contrapose h
        simp_all
        rw [← h1] at h3
        simp at h3
        exact h3
      apply index_tail_minus_one at h4
      simp only [head?_cons, Option.some.injEq, h5, tail_cons, ← h1, Option.map_some,
        false_or] at h4
      simp [← h1, h4]
    · have h3 := enter_queue_nodup e s
      intro i hik
      apply enter_queue_nodup_elements h1
      linarith

/- If n is in the sth queue at position k, then for l≤k, it has index k-l in the (s+l)th queue -/
lemma enter_queue_succ (h : List.idxOf? n (enter_queue e s) = some k) (h1 : l ≤ k) :
    n ∈ enter_queue e (s+l) ∧ List.idxOf? n (enter_queue e (s+l)) = some (k - l) := by
  have h2 := idxOf?_mem (id (Eq.symm h))
  have h3 := h2
  apply ne_nil_of_mem at h2
  apply ne_nil_iff_exists_cons.mp at h2
  obtain ⟨a, ⟨T, h2⟩⟩ := h2
  rw [h2] at h
  revert n
  induction l with | zero | succ l ih
  · simp_all
  · intro n hn hk
    have ⟨h3, h4⟩ : n ∈ enter_queue e (s + l) ∧ idxOf? n (enter_queue e (s + l)) = some (k - l) := by
      apply ih (le_of_succ_le h1)
      simp_all only [mem_cons, forall_eq_or_imp]
      exact hk
    have h5 : n ∈ (enter_queue e (s + l)).tail := by
      rw [index_tail]
      use k-l
      simp only [ge_iff_le, Nat.le_sub_of_add_le' h1, idxOf?_getElem? h4.symm, and_self]
    constructor
    · simp [enter_queue, h5]
    · apply enter_queue_dec_stage at h5
      simp [← add_assoc, h5]
      use k-l
      grind

/- The element that has been emitted at stage s, if it exists -/
def new_element (e s : ℕ) : Option ℕ := (enter_queue e s).head?

/- If n is in the sth queue at position k, it is enumerated at stage s+k -/
lemma enter_queue_enum_exact (h : List.idxOf? n (enter_queue e s) = some k) :
    new_element e (s+k) = n := by
  have h1 : k ≤ k := by rfl
  apply enter_queue_succ h at h1
  simp only [tsub_self] at h1
  obtain ⟨_, h1⟩ := h1
  rw [eq_comm, new_element, index_head, ← idxOf?_getElem?_iff]
  · exact id (Eq.symm h1)
  · tauto

/- The stage at which n is enumerated (if any).
Note that this is *not* the stage at which ϕ_e(n)↓, as n may wait in the enter_queue. -/
def enum_stage (e n : ℕ) : Part ℕ := Nat.rfind (fun s => (new_element e s == some n))

lemma enum_stage_spec (s : ℕ) (h : s ∈ enum_stage e n) : new_element e s == some n := by
  have h1 := rfind_spec h
  simp_all only [Part.coe_some, Part.mem_some_iff, Bool.true_eq, beq_iff_eq, BEq.rfl]

lemma enum_stage_min (s t : ℕ) (h : s ∈ enum_stage e n) (ht : t < s) :
    ¬ (new_element e t == some n) := by
  simp_all only [enum_stage, Part.coe_some, mem_rfind, Part.mem_some_iff, Bool.true_eq, beq_iff_eq,
    Bool.false_eq, beq_eq_false_iff_ne, ne_eq, not_false_eq_true]

/- If n ∈ W_e, then its enumeration stage exists. -/
lemma enum_stage_exists (e n : ℕ) (h : n ∈ W e) : (enum_stage e n).Dom := by
  simp [enum_stage]
  apply mem_W_ϕ.mp at h
  apply (enter_queue_mem e n).mpr at h
  have h1 : ∃ s k, List.idxOf? n (enter_queue e s) = some k := by
    obtain ⟨s, h⟩ := h
    use s
    have h2 : (idxOf? n (enter_queue e s)).isSome := by
      exact isSome_idxOf?.mpr h
    exact Option.isSome_iff_exists.mp h2
  obtain ⟨s, ⟨k, h1⟩⟩ := h1
  apply enter_queue_enum_exact at h1
  use s+k

/- If n is in a queue, it is eventually enumerated -/
lemma enter_queue_enum (h : n ∈ (enter_queue e s)) : ∃ t, new_element e t = n := by
  have ⟨k, h1⟩ : ∃ k, List.idxOf? n (enter_queue e s) = some k :=
    Option.isSome_iff_exists.mp (isSome_idxOf?.mpr h)
  apply enter_queue_enum_exact at h1
  use s+k

/- If n is in the sth queue at position k, it is in no queue after the (s+k)th -/
lemma enter_queue_exit_exact (h : List.idxOf? n (enter_queue e s) = some k) :
    ∀ t, n ∉ enter_queue e (s + k + t + 1) := by
  intro t
  have h1 := enter_queue_halts (idxOf?_mem (id (Eq.symm h)))
  have ⟨r, h2⟩ := ϕ_halts_runtime_exists.mp (ϕ_complete.mpr
    (Exists.intro s h1))
  apply (ϕNew_runtime_iff e n r).mpr at h2
  have h3 : r ≤ s := by
    simp only [ϕNew_runtime_iff] at h2
    apply runtime_min at h2
    contrapose h2
    push Not
    apply not_le.mp at h2
    use s
  have h4 : ∀ i, Disjoint (ϕNew e r) (ϕNew e (s+k+1+i)) := by
    intro i
    refine Disjoint.symm (ϕNew_disjoint_gt ?_)
    linarith
  simp [Finset.disjoint_left] at h4
  induction t with | zero | succ t ih
  <;> nth_rw 1 [enter_queue]
  <;> simp only [mem_append, not_or]
  · constructor
    · cases hL : enter_queue e (s+k) with | nil | cons a T
      · simp_all
      · have h5 := enter_queue_nodup e (s+k)
        have h6 := enter_queue_enum_exact h
        unfold new_element at h6
        simp_all only [nodup_cons, head?_cons, Option.some.injEq, tail_cons, not_false_eq_true]
    · simp only [Finset.mem_sort]
      exact h4 0 h2
  · constructor
    · contrapose ih
      exact mem_of_mem_tail ih
    · apply (h4 (t+1)) at h2
      simp_all [Nat.add_right_comm (s + k) 1 (t + 1)]

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

/- The sequence of enumerated elements -/
def Wenum (e : ℕ) : Stream' (Option ℕ) := new_element e

instance Wenum_dec (e : ℕ) : DecidablePred (fun k => ∃ s, Wenum e k = some s) := by
  simp [DecidablePred, Wenum, new_element]
  intro n
  have h (L : List ℕ) : (∃ s, L.head? = some s) ↔ (L ≠ []) := by
    constructor
    <;> intro h
    · have ⟨s, h⟩ := h
      refine List.ne_nil_of_length_pos (List.length_pos_iff_exists_mem.mpr ?_)
      exact ⟨s, List.mem_of_mem_head? h⟩
    · contrapose h
      push Not at h
      exact List.head?_eq_none_iff.mp (Option.eq_none_iff_forall_ne_some.mpr h)
  simp only [h (enter_queue e n), ne_eq]
  exact instDecidableNot

instance Wenum_comp : Computable (Wenum e)  := by
  unfold Wenum new_element
  refine Computable.comp (Primrec.to_comp Primrec.list_head?) (enter_queue_comp e)

lemma ϕ_halts_Wenum (e n : ℕ) : ϕ_halts e n ↔ ∃ s, n = Wenum e s := by
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

/-- TODO : extract frequent lemmas? -/
theorem We_mem_TFAE (e n : ℕ) :
    [n ∈ W e,                  --1
     ∃ s, n ∈ W_s e s,         --2
     ϕ_halts e n,              --3
     ∃ s, n = Wenum e s,       --4
     ∃ s, ϕ_s_halts e s n,     --5
    ].TFAE := by
  tfae_have 1 ↔ 2 := W_mem_iff_W_s
  tfae_have 3 ↔ 4 := ϕ_halts_Wenum e n
  tfae_have 2 ↔ 5 := by
    apply exists_congr
    intro a
    exact W_s_ϕ_s
  tfae_have 3 ↔ 5 := ϕ_complete
  tfae_finish

/-- TODO: prove a constructive version, then generalize to exists? -/
/- If ϕNew stabilizes, then eventually the queue depletes.
Indeed iff is true, see TFAE below. -/

lemma queue_depletes (h : (W e).Finite) :
    ∃ t, ∀ s ≥ t, enter_queue e s = [] := by
  rw [We_finite_iff_ϕNew_stabilizes] at h
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
    grind
  have hs : s ≥ t := by linarith
  have hs1 := enter_queue_ϕNewList e hs
  have hi1 : ∀ i, ϕNewList e (t+i+1) = [] := by
    intro i
    rw [← toFinset_eq_empty_iff]
    unfold ϕNewList
    simp
    grind
  simp_all only [gt_iff_lt, ge_iff_le, map_const', length_range, flatten_replicate_nil, append_nil]
  rw [← toFinset_eq_empty_iff]
  ext x
  simp only [mem_toFinset, Finset.notMem_empty, iff_false]
  grind

/-- TODO: the deepest case of this proof is truly horrible, and reused below. Extract! Fix!-/
lemma Wenum_finite_iff (e : ℕ) : (W e).Finite ↔ ∃ s, ∀ t ≥ s, Wenum e t = Option.none := by
  constructor
  · intro h
    have ⟨s, h1⟩ := queue_depletes h
    use s
    intro t ht
    simp_all only [Wenum, new_element, head?_eq_none_iff]
  · rw [We_finite_iff_ϕNew_stabilizes]
    intro ⟨t, h⟩
    use t
    intro s h1
    simp only [Wenum, new_element, head?_eq_none_iff] at h
    have h2 : enter_queue e s = [] := by
      apply h
      exact le_of_succ_le h1
    cases s with | zero | succ s
    · tauto
    · unfold enter_queue at h2
      simp only [append_eq_nil_iff] at h2
      obtain ⟨h2, h3⟩ := h2
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have : a ∈ (ϕNew e (s + 1)).sort (fun a b ↦ a ≤ b) := by
        exact (Finset.mem_sort fun a b ↦ a ≤ b).mpr ha
      contrapose h3
      exact ne_nil_of_mem this


lemma Wenum_infinite_iff (e : ℕ) : (W e).Infinite ↔ ∀ s, ∃ t ≥ s, ∃ n, Wenum e t = some n := by
  have h := Wenum_finite_iff e
  have h1 : ¬ (W e).Finite ↔ (W e).Infinite := Iff.symm (Eq.to_iff rfl)
  simp_all [Option.ne_none_iff_exists']

-- the following are here just to prove the TFAE statement
lemma queue_depletes_implies_ϕNew_stabilizes (h : ∃ t, ∀ s ≥ t, enter_queue e s = []) :
    ∃ t, ∀ s ≥ t, ϕNew e s = ∅ := by
  obtain ⟨t, h⟩ := h
  use t
  intro s hts
  have h1 := h s hts
  by_cases hs : s = 0
  · simp [hs]
    rfl
  · cases s with | zero | succ s
    · tauto
    · unfold enter_queue at h1
      simp only [append_eq_nil_iff] at h1
      obtain ⟨h2, h3⟩ := h1
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have : a ∈ (ϕNew e (s + 1)).sort (fun a b ↦ a ≤ b) := by
        exact (Finset.mem_sort fun a b ↦ a ≤ b).mpr ha
      contrapose h3
      exact ne_nil_of_mem this


lemma Ws_stabilizes_implies_We_eq_Ws (h : ∃ t, ∀ s ≥ t, W_s e s = W_s e t) :
    ∃ t, W e = W_s e t := by
  obtain ⟨t, h⟩ := h
  use t
  ext x
  rw [W_mem_iff_W_s]
  constructor
  <;> intro h1
  · obtain ⟨s, h1⟩ := h1
    by_cases hts : s > t
    · grind
    · exact W_s_mono (Nat.le_of_not_lt hts) h1
  · grind

lemma We_finite_iff_We_eq_Ws (h : ∃ t, W e = W_s e t) : (W e).Finite := by
  obtain ⟨t, h⟩ := h
  rw [h]
  exact Finset.finite_toSet (W_s e t)

lemma WsNew_stabilizes_Ws_stabilizes (e : ℕ) (h : ∃ t, ∀ s ≥ t, ϕNew e s = ∅) :
    ∃ t, ∀ s ≥ t, W_s e s = W_s e t := by
  obtain ⟨t, h⟩ := h
  use t
  intro s
  have h1 : ∀ s ≥ t, W_s e s = W_s e (s-1) := by
    intro s h1
    induction s with | zero | succ s ih
    · tauto
    · simp only [add_tsub_cancel_right]
      apply h at h1
      rw [ϕNew_eq_Ws_diff] at h1
      simp only [add_tsub_cancel_right, Finset.sdiff_eq_empty_iff_subset] at h1
      exact subset_antisymm h1 (W_s_mono (Nat.le_add_right s 1))
  induction s with | zero | succ s ih
  <;> grind

theorem We_finite_TFAE (e : ℕ) :
    [(W e).Finite,                          --1
      ∃ t, ∀ s ≥ t, ϕNew e s = ∅,           --2
      ∃ t, ∀ s ≥ t, W_s e s = W_s e t,      --3
      ∃ t, W e = W_s e t,                   --4
      ∃ t, ∀ s ≥ t, enter_queue e s = [],   --5
      ∃ t, ∀ s ≥ t, Wenum e s = Option.none --6
    ].TFAE := by
  tfae_have 1 → 5 := queue_depletes
  tfae_have 5 → 2 := queue_depletes_implies_ϕNew_stabilizes
  tfae_have 2 → 3 := WsNew_stabilizes_Ws_stabilizes e
  tfae_have 3 → 4 := Ws_stabilizes_implies_We_eq_Ws
  tfae_have 4 → 1 := We_finite_iff_We_eq_Ws
  tfae_have 1 ↔ 6 := Wenum_finite_iff e
  tfae_finish

theorem We_infinite_TFAE (e : ℕ) :
    [(W e).Infinite,                         --1
      ∀ t, ∃ s ≥ t, ϕNew e s ≠ ∅,        --2
      ∀ t, ∃ s ≥ t, W_s e s ≠ W_s e t,       --3
      ∀ t, W e ≠ W_s e t,                    --4
      ∀ t, ∃ s ≥ t, enter_queue e s ≠ [],   --5
      ∀ t, ∃ s ≥ t, ∃ n, Wenum e s = some n  --6
    ].TFAE := by
    have h := tfae_not_iff.mpr (We_finite_TFAE e)
    simp only [map] at h
    push Not at h
    simp only [Finset.nonempty_iff_ne_empty, Option.ne_none_iff_exists'] at h
    exact h
