/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.Phi
import Mathlib.Data.WSeq.Basic

/-
# ϕₑ and Wₑ
This file contains the definitions most commonly used by working computability theorists:
the use functions ϕₑ, the enumerable sets Wₑ,
and their stage versions ϕ_{e, s} and W_{e, s}.
-/

namespace Computability

open Nat
open Nat.Partrec
open Nat.Partrec.Code


/- The elements that will enter W_e at stage s. Note they are not in W_s! -/
def W_s_new (e s : ℕ) : List ℕ :=
  (List.range (s+1)).filter (λ n => (Phi_s_halts e (s+1) n ∧ ¬ Phi_s_halts e s n))

lemma W_s_new_eq (e s : ℕ) : (W_s_new e s).toFinset = (W_s e (s+1)) \ (W_s e s) := by
  simp [W_s_new, W_s]
  apply subset_antisymm
  · intro x
    simp
    intro h1 h2 h3
    · constructor
      · simp [h1, h2]
      · simp [h3]
  · intro x
    simp
    intro h1 h2 h3
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

lemma W_s_new_is_new (e s : ℕ) : (W_s_new e s).toFinset ∩ (W_s e s) = ∅ := by
  rw [W_s_new_eq]
  simp

/- x appears as a new element at its runtime -/
lemma W_s_new_runtime (y e s : ℕ) : y ∈ W_s_new e s ↔ s ∈ runtime e y := by
  simp [runtime, rfindOpt]
  constructor
  · simp [W_s_new, W_s]
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
    simp [W_s_new]
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
| s + 1 => (W_prefix e s) ++ (W_s_new e s)

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
      simp [W_s_new]
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
      simp [W_prefix, W_s_new, W_s, ← List.mem_toFinset, ← hs] at h
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
      rw [← List.mem_toFinset, W_s_new_eq] at h1
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

def W_seq (e : ℕ) : Stream'.Seq ℕ :=
  let init := W_prefix e 0
  ⟨W_stream e 1 init, by sorry
  ⟩

partial def W_seq (e : ℕ) : WSeq ℕ :=
  Seq.corec (fun (state : ℕ × List ℕ) =>
    let (s, remaining) := state
    match remaining with
    | []   =>
      let new := W_s_new e s
      match new with
      | []      => Option.none  -- diverge if no new element at this stage
      | .cons a tail => some (a, (s + 1, tail))
    | .cons a tail => some (a, (s, tail))
  ) (0, [])

open Stream'.Seq

lemma W_prefix_true (e s n : ℕ) :
  n ∈ (W_prefix e s) ↔ n ∈ W_seq e := by
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
