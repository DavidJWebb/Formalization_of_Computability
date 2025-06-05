/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.SetPrimRec
import FormalizationOfComputability.CodeDecode
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Linarith
import Mathlib.Data.Seq.Seq
import Mathlib.Data.WSeq.Basic

set_option warningAsError false

/-
# ϕₑ and Wₑ
This file contains the definitions most commonly used by working computability theorists :
the use functions ϕₑ and the enumerable sets Wₑ.
-/

namespace Nat.Partrec.Code

/- noncomputable def μ (P : ℕ → Prop) [DecidablePred P] (h : ∃ n, P n) : ℕ :=
Nat.find h -/

/- ϕₑ,ₛ(_). Following Soare, we require the index, input, and output to be less than s -/
def Phi_s (e s n : ℕ) : Option ℕ :=
    if (e < s) ∧ (∃ (y : ℕ), (y < s) ∧ y ∈ evaln s (ofNatCode e) n)
    then evaln s (ofNatCode e) n
    else Option.none

/- ϕₑ(_) -/
def Phi (e : ℕ) : ℕ →. ℕ :=
    eval (ofNatCode e)

/- halting -/
def Phi_s_halts (e s n : ℕ) : Prop :=
    ∃ x, x ∈ Phi_s e s n
def Phi_halts (e n : ℕ) : Prop :=
    ∃ x, x ∈ Phi e n
def Phi_s_diverges (e s n : ℕ) : Prop :=
    ¬ Phi_s_halts e s n
def Phi_diverges (e n : ℕ) : Prop :=
    ¬ Phi_halts e n

instance (e s n : ℕ): Decidable (Phi_s_halts e s n) := by
  unfold Phi_s_halts Phi_s
  simp
  have h : Decidable (∃ x, evaln s (ofNatCode e) n = some x) := by
     match evaln s (ofNatCode e) n with
    | some x        => exact isTrue ⟨x, rfl⟩
    | Option.none   => exact isFalse (λ ⟨x, h⟩ => Option.noConfusion h)
  apply instDecidableAnd

/- Wₑ,ₛ = {n | n ≤ s ∧ ϕₑ,ₛ(n)↓}, i.e. those n for which ϕₑ(x) halts in < s steps -/
def W_s (e s : ℕ) : Finset ℕ :=
  (Finset.range s).filter (Phi_s_halts e s)
/- Wₑ = {n | ϕₑ(n)↓} -/
def W (e : ℕ) : Set ℕ := (Phi e).Dom

lemma halt_input_bound (e s n : ℕ) (h : Phi_s_halts e s n) :
    n < s := by
  simp [Phi_s_halts, Phi_s] at h
  obtain ⟨x, hx⟩ := h.right
  apply Code.evaln_bound
  exact hx

lemma halt_output_bound (e s y n : ℕ) (h : y ∈ (Phi_s e s n)) :
  y < s := by
  simp [Phi_s] at h
  obtain ⟨⟨h1, ⟨z, ⟨h2, h3⟩⟩⟩, h⟩ := h
  have h4 : y = z := by
    simp [h] at h3
    exact h3
  rw [h4]
  exact h2

lemma halt_index_bound (e s n : ℕ) (h : Phi_s_halts e s n) :
    e < s := by
  simp [Phi_s_halts, Phi_s] at h
  exact h.left.left

lemma halt_stage_gt_zero (e s n : ℕ) (h : Phi_s_halts e s n) : s > 0 := by
  by_contra h1
  simp at h1
  revert h
  rw [h1]
  unfold Phi_s_halts Phi_s
  simp

lemma phi_partrec (e : ℕ) : Partrec (Phi e) := by
  unfold Phi
  rw [exists_code]
  use ofNatCode e

/- The Wₑ are Σ01 -/
lemma W_Sigma01 (e : ℕ) : Sigma01 (W e) := by
  unfold Sigma01 W set_partrec
  use λ n => (Phi e n).map (λ _ => ())
  constructor
  · refine Partrec.map ?_ ?_
    constructor
    · exact phi_partrec e
    · refine Partrec.nat_iff.mp ?_
      apply Computable.partrec
      exact Computable.id
    · refine Primrec₂.to_comp ?_
      exact Primrec₂.const ()
  · rfl

/- Sigma01 sets can be written as Wₑ -/
lemma Sigma01_is_W (X : Set ℕ) : Sigma01 X → ∃ e, X = W e := by
· intro h
  unfold Sigma01 set_partrec at h
  obtain ⟨f, ⟨h1, h2⟩⟩ := h
  let f_nat : ℕ →. Nat :=
  λ n => (f n).map (λ _ => 1)
  have h3 : Partrec f_nat := by
    refine Partrec.nat_iff.mp ?_
    refine Partrec.map h1 ?_
    refine Primrec₂.to_comp ?_
    exact Primrec₂.const 1
  have h4 : f.Dom = f_nat.Dom := by
    rfl
  rw [exists_code] at h3
  obtain ⟨c, h3⟩ := h3
  rw [← h2, h4]
  use c.encodeCode
  unfold W
  unfold Phi
  rw [← ofNatCode_encode c]
  rw [← h3]

/- The Σ01 sets are exactly the Wₑ -/
lemma Sigma01_iff_W (X : Set ℕ) : Sigma01 X ↔ ∃ e, X = W e := by
  constructor
  · exact Sigma01_is_W X
  · intro h
    obtain ⟨e, h⟩ := h
    rw [h]
    exact W_Sigma01 e

/- s < t → ϕ_{e,s}(n)↓ → ϕ_{e,t}(n)↓ -/
theorem phi_halts_mono (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_s_halts e s n) :
    Phi_s_halts e t n := by
  revert h1
  simp [Phi_s_halts, Phi_s]
  intro h1 x h2 h3 y h4
  constructor
  · constructor
    · linarith
    · use x
      constructor
      · linarith
      · apply evaln_mono h h3
  · use x
    apply evaln_mono h h3

/- s < t → ϕ_{e,t}(n)↑ → ϕ_{e,s}(n)↑ -/
theorem phi_halts_mono_reverse (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_s_diverges e t n) :
  Phi_s_diverges e s n := by
  contrapose h1
  revert h1
  unfold Phi_s_diverges
  rw [not_not, not_not]
  exact fun h1 ↦ phi_halts_mono e s t n h h1

/- There is a least time that it takes for ϕ to halt (if it does)-/
def runtime (e n : ℕ) : Part ℕ :=
  rfindOpt (fun s => if (Phi_s e (s+1) n).isSome then some s else Option.none)

/- Statements involving runtime can appear to have off-by-one errors.
This is because if x has runtime s, x ∉ W_{e,s} but instead x ∈ W_{e, s+1}. -/
theorem runtime_is_min (e n s : ℕ) : (s ∈ (runtime e n)) ↔
    Phi_s_halts e (s+1) n ∧ (∀ (t : ℕ), t < s → Phi_s_diverges e (t+1) n) := by
  constructor
  · intro h
    simp [runtime, rfindOpt] at h
    obtain ⟨⟨hs, hs2⟩, hs⟩ := h
    unfold Phi_s_halts
    constructor
    · rw [Option.isSome_iff_exists] at hs
      obtain ⟨a, h⟩ := hs
      use a
      exact h
    · intro t h
      apply hs2 at h
      unfold Phi_s_diverges Phi_s_halts
      rw [h]
      simp
  · intro ⟨h1, h2⟩
    apply Option.isSome_iff_exists.mpr at h1
    simp [runtime, rfindOpt]
    constructor
    · constructor
      · exact h1
      · intro m hm
        apply h2 at hm
        unfold Phi_s_diverges Phi_s_halts at hm
        push_neg at hm
        exact Option.eq_none_iff_forall_ne_some.mpr hm
    · exact h1

/- ϕₑ(n)↓ ↔ ∃ s, ϕₑ,ₛ(n)↓ -/
theorem phi_halts_stage_exists (e n : ℕ) : Phi_halts e n ↔ ∃ s, Phi_s_halts e s n := by
  unfold Phi_s_halts Phi_halts Phi_s Phi
  simp [evaln_complete]
  constructor
  · intro ⟨x, ⟨k, h⟩⟩
    use e+x+k+1
    constructor
    · constructor
      · linarith -- e < e+k+x+1
      · use x
        constructor
        · linarith -- k < e+k+x+1
        · apply evaln_mono
          rotate_left
          · exact h
          · linarith
    · use x
      apply evaln_mono
      rotate_left
      · exact h
      · linarith
  · intro ⟨s, ⟨⟨h, ⟨y, ⟨hys, h1⟩⟩⟩, ⟨x, h2⟩⟩⟩
    use x
    use s

theorem phi_halts_runtime_exists (e n : ℕ) : Phi_halts e n ↔ ∃ y, y ∈ runtime e n := by
  constructor
  · intro h
    rw [phi_halts_stage_exists] at h
    obtain ⟨s, h⟩ := h
    have h1 : ∃ y, y ∈ rfindOpt (λ s => Phi_s e s n) := by
      rw [← Part.dom_iff_mem, rfindOpt_dom]
      use s
      exact h
    obtain ⟨y, h1⟩:= h1
    simp [min, rfindOpt] at h1
    obtain ⟨t, ⟨⟨h2, h3⟩, h1⟩⟩ := h1
    have h5 : ∃ y, Phi_s e t n = some y := ⟨y, h1⟩
    apply halt_stage_gt_zero at h5
    rw [gt_iff_lt, lt_iff_add_one_le, zero_add] at h5
    use t-1
    simp [runtime, rfindOpt]
    rw [Nat.sub_add_cancel]
    rotate_left
    exact h5
    constructor
    · constructor
      · exact h2
      · intro m h
        apply h3
        exact add_lt_of_lt_sub h
    · exact h2
  · intro ⟨y, h⟩
    rw [runtime_is_min] at h
    rw [phi_halts_stage_exists]
    use y+1
    exact h.left


/- ϕₑ,ₛ(x)↓ ↔ x ∈ Wₑ,ₛ -/
lemma W_s_Phi_s (e s n : ℕ) : n ∈ W_s e s ↔ Phi_s_halts e s n := by
unfold W_s Phi_s_halts
simp
intro x h
apply halt_input_bound e s n
unfold Phi_s_halts
use x
exact h

/- ϕₑ(x)↓ ↔ x ∈ Wₑ -/
lemma mem_W_phi (e n : ℕ) : n ∈ W e ↔ Phi_halts e n := by
unfold W Phi_halts
exact Part.dom_iff_mem

/- W_{s} ⊆ W_{e, s+1}  -/
lemma W_s_mono (e s t : ℕ) (h : s ≤ t): (W_s e s) ⊆ (W_s e t) := by
  intro x
  simp [W_s]
  intro h1 h2
  constructor
  · linarith
  · apply phi_halts_mono e s
    · exact h
    · exact h2

lemma W_s_mono_reverse (e s t : ℕ) (h : t ≤ s) : (W_s e t) ⊆ (W_s e s) := by
  intro x
  simp [W_s]
  intro h1 h2
  constructor
  · linarith
  · apply phi_halts_mono e t
    · exact h
    · exact h2


/- Wₑ,ₛ ⊆ Wₑ  -/
theorem W_s_subset_W (e s : ℕ) : (W_s e s).toSet ⊆ W e := by
  intro x
  simp [W_s, W]
  intro h h1
  rw [← Phi_halts, phi_halts_stage_exists]
  use s

/- Wₑ = ⋃ₛ Wₑ,ₛ -/
theorem W_mem_iff_W_s (e n: ℕ) : n ∈ W e ↔ ∃ s, n ∈ W_s e s :=by
constructor
· intro h
  apply Part.dom_iff_mem.mp at h
  rw [← Phi_halts] at h
  rw [phi_halts_stage_exists] at h
  obtain ⟨s, h⟩ := h
  use s
  rw [W_s_Phi_s]
  exact h
· intro h
  obtain ⟨s, h⟩ := h
  apply W_s_subset_W
  exact h

theorem W_eq_union_W_s (e : ℕ) : W e = ⋃ (s : ℕ), W_s e s := by
ext x
rw [W_mem_iff_W_s]
simp

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

lemma nodup_W_prefix (e s : ℕ) : List.Nodup (W_prefix e s) := by
  induction' s with s ih
  · unfold W_prefix
    simp
  · simp [W_prefix]
    sorry

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

/- lemma W_prefix_mono_plus_1 (e s : ℕ) :
    (W_prefix e s) <+: (W_prefix e (s+1)) := by
  simp [W_prefix] -/

lemma W_prefix_mono (e s t : ℕ) (h : s ≤ t) :
  (W_prefix e s) <+: (W_prefix e t) := by
  induction' t with t ih
  · simp at h
    rw [h]
  · by_cases h1 : s = t + 1
    · rw [h1]
    · have h2 : s ≤ t := by
        exact le_of_lt_succ (Nat.lt_of_le_of_ne h h1)
      apply ih at h2
      apply List.IsPrefix.trans h2
      simp [W_prefix]

partial def W_seq.aux (e k s : ℕ) (acc : List ℕ) : ℕ :=
  let new := (W_prefix e s).filter (· ∉ acc)
  let acc' := acc ++ new
  if h : k < acc'.length then acc'.get ⟨k, h⟩
  else W_seq.aux e k (s + 1) acc'

def listDiff {α : Type} [DecidableEq α] (l₁ l₂ : List α) : List α :=
  -- Returns the suffix of l₂ after removing the prefix l₁
  l₂.drop l₁.length

open Stream'

-- W_prefix

def prefix_union : (ℕ → List ℕ) → WSeq ℕ :=
  Seq.corec fun f =>
    match f 0 with
    | [] => some (Option.none, fun n => f (n+1))
    | .cons a _ => some (some a, fun n => (f n).tail)

def W_seq (e : ℕ) : WSeq ℕ := prefix_union (W_prefix e)

open Stream'.Seq

-- TODO: this must be rewritten (both statement and proof) to account for WSeq

lemma W_prefix_true (e s : ℕ) :
  W_prefix e s = (splitAt (W_prefix e s).length (W_seq e)).1 := by
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


-- #min_imports
