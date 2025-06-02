/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.SetPrimRec
import FormalizationOfComputability.CodeDecode
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Linarith

set_option warningAsError false

/-
# ϕₑ and Wₑ
This file contains the definitions most commonly used by working computability theorists :
the use functions ϕₑ and the enumerable sets Wₑ.
-/

namespace Nat.Partrec.Code

/- noncomputable def μ (P : ℕ → Prop) [DecidablePred P] (h : ∃ n, P n) : ℕ :=
Nat.find h -/

/- ϕₑ,ₛ(_). Following Soare, we require e, n, and y (the output) to be less than s -/

def Phi_stage (e s n : ℕ) : Option ℕ :=
    if (e < s) ∧ (∀ (y : ℕ), y ∈ evaln s (ofNatCode e) n → y < s)
    then evaln s (ofNatCode e) n
    else Option.none

/- ϕₑ(_) -/
def Phi (e : ℕ) : ℕ →. ℕ :=
    eval (ofNatCode e)

/- halting -/
def Phi_stage_halts (e s n : ℕ) : Prop :=
    ∃ (x : ℕ), x ∈ Phi_stage e s n
def Phi_halts (e n : ℕ) : Prop :=
    ∃ (x : ℕ), x ∈ Phi e n
def Phi_stage_diverges (e s n : ℕ) : Prop :=
    ¬ Phi_stage_halts e s n
def Phi_diverges (e n : ℕ) : Prop :=
    ¬ Phi_halts e n

instance (e s n : ℕ): Decidable (Phi_stage_halts e s n) := by
  unfold Phi_stage_halts Phi_stage
  simp
  have h1 : Decidable (e < s ∧ ∀ (y : ℕ), evaln s (ofNatCode e) n = some y → y < s) := by
    apply instDecidableAnd
  have h2 : Decidable (∃ x, evaln s (ofNatCode e) n = some x) := by
     match evaln s (ofNatCode e) n with
    | some x        => exact isTrue ⟨x, rfl⟩
    | Option.none   => exact isFalse (λ ⟨x, h⟩ => Option.noConfusion h)
  exact inferInstance

/- Wₑ,ₛ = {n | n ≤ s ∧ ϕₑ,ₛ(n)↓}, i.e. those n for which ϕₑ(x) halts in < s steps -/
def W_s (e s : ℕ) : Set ℕ :=
  (Finset.range s).filter (Phi_stage_halts e s)
/- Wₑ = {n | ϕₑ(n)↓} -/
def W (e : ℕ) : Set ℕ := (Phi e).Dom

lemma halt_input_bound (e s n : ℕ) (h : Phi_stage_halts e s n) :
    n < s := by
  simp [Phi_stage_halts, Phi_stage] at h
  obtain ⟨x, hx⟩ := h.right
  apply Code.evaln_bound
  exact hx

lemma halt_output_bound (e s y n : ℕ) (h : y ∈ (Phi_stage e s n)) :
  y < s := by
  simp [Phi_stage] at h
  have h2 : evaln s (ofNatCode e) n = some y := by exact h.right
  apply h.left.right at h2
  exact h2

lemma halt_index_bound (e s n : ℕ) (h : Phi_stage_halts e s n) :
    e < s := by
  simp [Phi_stage_halts, Phi_stage] at h
  exact h.left.left


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
lemma Sigma01_is_W (X : Set ℕ) : Sigma01 X → ∃ (e : ℕ), X = W e := by
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
lemma Sigma01_iff_W (X : Set ℕ) : Sigma01 X ↔ ∃ (e : ℕ), X = W e := by
  constructor
  · exact Sigma01_is_W X
  · intro h
    obtain ⟨e, h⟩ := h
    rw [h]
    exact W_Sigma01 e

/- s < t → ϕₑ,ₛ(n)↓ → ϕₑ,ₜ(n)↓ -/
theorem phi_halts_mono (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_stage_halts e s n) :
    Phi_stage_halts e t n := by
  revert h1
  simp [Phi_stage_halts, Phi_stage]
  intro h1 h2 y h3
  constructor
  · constructor
    · exact Nat.lt_of_lt_of_le h1 h
    · intro z hz
      have htz : evaln t (ofNatCode e) n = some y := by
        apply Nat.Partrec.Code.evaln_mono
        · exact h
        · exact h3
      simp [hz] at htz
      rw [htz]
      apply h2 at h3
      exact Nat.lt_of_lt_of_le h3 h
  · use y
    apply Nat.Partrec.Code.evaln_mono
    · exact h
    · exact h3

/- ϕₑ(n)↓ ↔ ∃ (s : ℕ), ϕₑ,ₛ(n)↓ -/
theorem phi_halts_runtime_exists (e n : ℕ) : Phi_halts e n ↔ ∃ (s : ℕ), Phi_stage_halts e s n := by
  unfold Phi_stage_halts Phi_halts Phi_stage Phi
  simp [evaln_complete]
  constructor
  · intro ⟨x, ⟨k, h⟩⟩
    use e+x+k+1
    constructor
    · constructor
      · linarith -- e < e+k+x+1
      · intro y h1
        apply (Nat.Partrec.Code.evaln_mono) at h
        · rw [h1] at h
          simp at h
          rw [h]
          linarith -- x < e+k+x+1
        · linarith -- k < e+k+x+1
    use x
    apply (Nat.Partrec.Code.evaln_mono) at h
    · exact h
    · linarith
  · intro ⟨s,⟨⟨h1,h2⟩,⟨x, h3⟩⟩⟩
    use x
    use s


theorem phi_halts_mono_reverse (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_stage_diverges e t n) :
  Phi_stage_diverges e s n := by
  contrapose h1
  revert h1
  unfold Phi_stage_diverges
  rw [not_not, not_not]
  exact fun h1 ↦ phi_halts_mono e s t n h h1

/- There is a least time that it takes for ϕ to halt (if it does)-/
def runtime (e n : ℕ) : Part ℕ :=
  rfindOpt (fun s => if (Phi_stage e (s+1) n).isSome then some s else Option.none)

/- Statements involving runtime often look they have off by one errors.
This is because runtime s is exact, while elements are only seen to enter W_e at stages t > s -/
theorem runtime_is_min (e n s : ℕ) : (s ∈ (runtime e n)) ↔
    Phi_stage_halts e (s+1) n ∧ (∀ (t : ℕ), t < s → Phi_stage_diverges e (t+1) n) := by
  constructor
  · intro h
    simp [runtime, rfindOpt] at h
    obtain ⟨⟨hs, hs2⟩, hs⟩ := h
    unfold Phi_stage_halts
    constructor
    · rw [Option.isSome_iff_exists] at hs
      obtain ⟨a, h⟩ := hs
      use a
      exact h
    · intro t h
      apply hs2 at h
      unfold Phi_stage_diverges Phi_stage_halts
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
        unfold Phi_stage_diverges Phi_stage_halts at hm
        push_neg at hm
        exact Option.eq_none_iff_forall_ne_some.mpr hm
    · exact h1

/- ϕₑ,ₛ(x)↓ ↔ x ∈ Wₑ,ₛ -/
lemma W_s_phi_stage (e s n : ℕ) : n ∈ W_s e s ↔ Phi_stage_halts e s n := by
unfold W_s Phi_stage_halts
simp
intro x h
apply halt_input_bound e s n
unfold Phi_stage_halts
use x
exact h

/- ϕₑ(x)↓ ↔ x ∈ Wₑ -/
lemma mem_W_phi (e n : ℕ) : n ∈ W e ↔ Phi_halts e n := by
unfold W Phi_halts
exact Part.dom_iff_mem

/- W_{s} ⊆ W_{e, s+1}  -/
lemma W_s_mono (e s : ℕ) : (W_s e s) ⊆ (W_s e (s+1)) := by
  intro x
  unfold W_s
  simp
  intro h h1
  constructor
  · linarith
  · apply phi_halts_mono e s
    · linarith
    · exact h1

/- Wₑ,ₛ ⊆ Wₑ  -/
theorem W_s_subset_W (e s : ℕ) : (W_s e s) ⊆ W e := by
  intro x
  simp [W_s, W]
  intro h h1
  rw [← Phi_halts, phi_halts_runtime_exists]
  use s


/- Wₑ = ⋃ₛ Wₑ,ₛ -/
theorem W_mem_iff_W_s (e n: ℕ) : n ∈ W e ↔ ∃ (s : ℕ), n ∈ W_s e s :=by
constructor
· intro h
  apply Part.dom_iff_mem.mp at h
  rw [← Phi_halts] at h
  rw [phi_halts_runtime_exists] at h
  obtain ⟨s, h⟩ := h
  use s
  rw [W_s_phi_stage]
  exact h
· intro h
  obtain ⟨s, h⟩ := h
  apply W_s_subset_W
  exact h

theorem W_eq_union_W_s (e : ℕ) : W e = ⋃ (s : ℕ), W_s e s := by
ext x
rw [W_mem_iff_W_s]
simp

/- The elements that have will W_e at stage s -/
def W_s_new (e s : ℕ) : Set ℕ := (W_s e (s+1)) \ (W_s e s)

/- x appears as a new element at its runtime -/
lemma W_s_new_runtime (x e s : ℕ) : x ∈ W_s_new e s ↔ s ∈ runtime e x := by
  simp [runtime, rfindOpt]
  constructor
  · simp [W_s_new, W_s]
    intro h1 h2 h3
    constructor
    · constructor
      · exact Option.isSome_iff_exists.mpr h2
      · have h4 : Phi_stage_halts e s x → x < s := by
          apply halt_input_bound
        have h5 : ¬Phi_stage_halts e s x := by
          by_contra h
          revert h3
          simp
          constructor
          · exact h4 h
          · exact h
        intro m hm
        apply phi_halts_mono_reverse e (m+1) at h5
        · unfold Phi_stage_diverges Phi_stage_halts at h5
          push_neg at h5
          exact Option.eq_none_iff_forall_ne_some.mpr h5
        · exact hm
    exact Option.isSome_iff_exists.mpr h2
  · intro ⟨⟨h, h1⟩, h2⟩
    clear h2
    constructor
    · apply Option.isSome_iff_exists.mp at h
      simp [W_s]
      constructor
      · apply halt_input_bound
        unfold Phi_stage_halts
        exact h
      · exact h
    · simp [W_s, Phi_stage_halts]
      intro h
      push_neg
      intro y
      by_cases h2 : s=0
      · simp [h2]
        unfold Phi_stage
        simp
      · have h3 : s - 1 < s := by
          exact sub_one_lt h2
        apply h1 at h3
        rw [sub_one_add_one_eq_of_pos] at h3
        · rw [Option.eq_none_iff_forall_not_mem] at h3
          exact h3 y
        · exact zero_lt_of_ne_zero h2

/- The elements in W_e enumerated at stage s-/
def W_enum (e : ℕ) : ℕ → List ℕ
| 0     => []
| s + 1 =>
  let prev := W_enum e (s - 1)
  let delta := (W_s_new e s).toList
  prev ++ delta.filter (λ n => n ∉ prev)

lemma W_s_eq_W_enum (e s : ℕ) : W_s e s = (W_enum e s).toFinset := by
  induction' s with s hs
  · unfold W_enum W_s Phi_stage
    simp
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro x
    simp only [Finset.mem_singleton, imp_self]
    simp
    intro h
    rw [h]
    unfold evaln
    rfl
  apply subset_antisymm
  · intro x
    have hs1 : (W_s e (s+1)) = (W_s_new e s).toFinset ∪  (W_s e s) := by
      rw [W_s_new_eq]
      simp
    unfold W_s W_enum
    simp
    intro h h1

  ·


-- TODO : create W_enum : ℕ →. ℕ gathering all W_enum_prefix

lemma inf_inc_sigma01_seq_is_delta01 (e : ℕ) (h1 : (W e).Infinite)
    (h2 : ∀ (n : ℕ), W_enum_prefix n n < W_enum_prefix (n+1) (n+1)) :
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
