/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.PrimRecFilter
import FormalizationOfComputability.Sets
import Mathlib.Tactic.Linarith
/-
# ϕₑ and Wₑ
This file contains the definitions most commonly used by working computability theorists:
the use functions ϕₑ, the enumerable sets Wₑ, and their computable
approximations ϕ_{e, s} and W_{e, s}.

In some sense Phi_s and Phi are merely wrappers for evaln and eval, respectively, modified
to match common computability theory notation.

## Main results

## Notation
- 'Delta01' is used to mean a set is computable
- 'Sigma01' is used to mean a set is partial computable
## References
- [R. I. Soare *Turing Computability - Theory and Applications*] [Soare2016]
-/


namespace Computability

abbrev Delta01 := computable_set
abbrev Sigma01 := partrec_set

open Nat
open Nat.Partrec
open Nat.Partrec.Code

/- Helper lemmas that ofNatCode and encodeCode are inverse functions. The latter
is present in Partrec.Code, but is marked as a private -/
lemma ofNatCode_encode (c : Code) :
    c = (ofNatCode (encodeCode c)) := by
  induction c with
  | zero => simp [encodeCode, ofNatCode]
  | succ => simp [encodeCode, ofNatCode]
  | left => simp [encodeCode, ofNatCode]
  | right => simp [encodeCode, ofNatCode]
  | pair cf cg ihf ihg =>
      simp [encodeCode, ofNatCode]
      simp [← ihf, ← ihg]
  | comp cf cg ihf ihg =>
      simp [encodeCode, ofNatCode]
      simp [← ihf, ← ihg]
  | prec cf cg ihf ihg =>
      simp [encodeCode, ofNatCode]
      simp [← ihf, ← ihg]
  | rfind' cf ihf =>
      simp [encodeCode, ofNatCode]
      exact ihf

lemma encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | n + 4 => by
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (div_le_self _ _) (div_le_self _ _))
          (succ_le_succ (le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← bit_decomp n, ← bit_decomp n.div2]
    simp only [ofNatCode.eq_5]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, ofNatCode, IH, IH1, IH2, bit_val]

/- ϕₑ,ₛ(n), the eth Turing program evaluated for s steps on input n.
Following Soare, we require the index, input, and output to be less than s -/
def Phi_s (e s n : ℕ) : Option ℕ :=
    if (e < s) ∧ (∃ y < s, y ∈ evaln s (ofNatCode e) n)
    then evaln s (ofNatCode e) n
    else Option.none

/- ϕₑ(n), the eth Turing program evaluated on input n -/
def Phi (e : ℕ) : ℕ →. ℕ :=
    eval (ofNatCode e)

/- ϕₑ,ₛ(n)↓ iff it has an output -/
def Phi_s_halts (e s n : ℕ) : Prop :=
    ∃ x, x ∈ Phi_s e s n

/- ϕₑ(n)↓ iff it has an output -/
def Phi_halts (e n : ℕ) : Prop :=
    ∃ x, x ∈ Phi e n

/- ϕₑ,ₛ(n)↑ iff it doesn't halt -/
def Phi_s_diverges (e s n : ℕ) : Prop :=
    ¬ Phi_s_halts e s n

/- ϕₑ(n)↑ iff it doesn't halt -/
def Phi_diverges (e n : ℕ) : Prop :=
    ¬ Phi_halts e n


instance (e s n : ℕ) : Decidable (∃ x, x ∈ Phi_s e s n) := by
  simp [Phi_s]
  have h : Decidable (∃ x, evaln s (ofNatCode e) n = some x) := by
     match evaln s (ofNatCode e) n with
    | some x        => exact isTrue ⟨x, rfl⟩
    | Option.none   => exact isFalse (λ ⟨x, h⟩ => Option.noConfusion h)
  apply instDecidableAnd

/- ϕₑ,ₛ(n) is decidable -/
instance (e s n : ℕ): Decidable (Phi_s_halts e s n) := by
  simp [Phi_s_halts, Phi_s]
  have h : Decidable (∃ x, evaln s (ofNatCode e) n = some x) := by
     match evaln s (ofNatCode e) n with
    | some x        => exact isTrue ⟨x, rfl⟩
    | Option.none   => exact isFalse (λ ⟨x, h⟩ => Option.noConfusion h)
  apply instDecidableAnd

/- Wₑ,ₛ = the domain of ϕₑ,ₛ. As all inputs n ≥ s do not halt,
this set is necessarily finite. -/
def W_s (e s : ℕ) : Finset ℕ :=
  (Finset.range s).filter (Phi_s_halts e s)

/- Wₑ = {n | ϕₑ(n)↓} -/
def W (e : ℕ) : Set ℕ := (Phi e).Dom

/- If ϕₑ,ₛ(n)↓, then n < s -/
lemma halt_input_bound (e s n : ℕ) (h : Phi_s_halts e s n) :
    n < s := by
  simp [Phi_s_halts, Phi_s] at h
  obtain ⟨x, hx⟩ := h.right
  apply Code.evaln_bound
  exact hx

/- If ϕₑ,ₛ(n) = y, then y < s -/
lemma halt_output_bound (e s n y : ℕ) (h : y ∈ (Phi_s e s n)) :
  y < s := by
  simp [Phi_s] at h
  obtain ⟨⟨h1, ⟨z, ⟨h2, h3⟩⟩⟩, h⟩ := h
  simp_all

/- If ϕₑ,ₛ(n)↓, then e < s -/
lemma halt_index_bound (e s n : ℕ) (h : Phi_s_halts e s n) :
    e < s := by
  simp_all [Phi_s_halts, Phi_s]

/- Helper lemmas - ϕ_{e, 0}(n)↑ -/
lemma halt_stage_gt_zero (e s n : ℕ) (h : Phi_s_halts e s n) : s > 0 := by
  simp [Phi_s_halts, Phi_s] at h
  linarith

lemma stage_zero_diverges (e n : ℕ) : Phi_s_diverges e 0 n := by
  simp [Phi_s_diverges, Phi_s_halts, Phi_s]


open Primrec

/- ϕₑ,ₛ is a primitive recursive function -/
lemma phi_s_primrec (e s : ℕ) : Primrec (Phi_s e s) := by
  have h : Primrec (evaln s (ofNatCode e)) := by
      apply primrec_evaln.comp (pair (pair (const s) (const (ofNatCode e))) Primrec.id)
  unfold Phi_s
  apply Primrec.ite ?_ h (Primrec.const Option.none)
  apply PrimrecPred.and (PrimrecRel.comp Primrec.nat_lt (Primrec.const e) (Primrec.const s)) ?_
  apply PrimrecPred.bounded_exists
  simp [PrimrecRel, Primrec₂]
  exact PrimrecRel.comp Primrec.eq (Primrec.comp h snd) (option_some_iff.mpr fst)

lemma phi_s_halts_primrec (e s : ℕ) : PrimrecPred (Phi_s_halts e s) := by
  have h (n : ℕ) : (∃ x, Phi_s e s n = some x) ↔ (∃ x < s, Phi_s e s n = some x) := by
    constructor
    · intro ⟨x, h⟩
      use x
      constructor
      · apply halt_output_bound e s n
        exact h
      · exact h
    · simp_all
  unfold Phi_s_halts
  simp [PrimrecPred]
  simp [h]
  apply PrimrecPred.bounded_exists
  apply PrimrecRel.comp₂ Primrec.eq
  · exact comp₂ (phi_s_primrec e s) (Primrec₂.right)
  · exact comp₂ option_some Primrec₂.left

/- ϕₑ is a partial computable function -/
theorem phi_partrec (e : ℕ) : Nat.Partrec (Phi e) := by
  unfold Phi
  rw [Code.exists_code]
  use ofNatCode e

/- The Wₑ,ₛ are primitive recursive-/
lemma W_s_Primrec (e s : ℕ) : primrec_set (W_s e s) := by
  simp [primrec_set, W_s]
  use Phi_s_halts e s
  constructor
  · apply Primrec.ite
    · exact phi_s_halts_primrec e s
    · exact Primrec.const true
    · exact Primrec.const false
  · intro x
    constructor
    · intro ⟨h, h1⟩
      exact decide_eq_true h1
    · intro h
      simp at h
      constructor
      · exact halt_input_bound e s x h
      · exact h

/- The Wₑ are Σ01 -/
lemma W_Sigma01 (e : ℕ) : Sigma01 (W e) := by
  unfold Sigma01 W partrec_set
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
  unfold Sigma01 partrec_set at h
  obtain ⟨f, ⟨h1, h2⟩⟩ := h
  let f_nat : ℕ →. Nat :=
  λ n => (f n).map (λ _ => 1)
  have h3 : Nat.Partrec f_nat := by
    refine Partrec.nat_iff.mp ?_
    refine Partrec.map h1 ?_
    refine Primrec₂.to_comp ?_
    exact Primrec₂.const 1
  have h4 : f.Dom = f_nat.Dom := by
    rfl
  rw [Code.exists_code] at h3
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
  · simp_all [W_Sigma01]

/- Monotonicity of halting: if s < t and ϕ_{e,s}(n)↓, then ϕ_{e,t}(n)↓ -/
lemma phi_halts_mono (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_s_halts e s n) :
    Phi_s_halts e t n := by
  revert h1
  simp [Phi_s_halts, Phi_s]
  intro _ x _ h3 _ _
  constructor
  · constructor
    · linarith
    · use x
      constructor
      · linarith
      · apply evaln_mono h h3
  · use x
    apply evaln_mono h h3

/- Reverse monotonicity of halting: if s < t and ϕ_{e,t}(n)↑, then ϕ_{e,s}(n)↑ -/
lemma phi_halts_mono_reverse (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_s_diverges e t n) :
  Phi_s_diverges e s n := by
  contrapose h1
  revert h1
  unfold Phi_s_diverges
  rw [not_not, not_not]
  exact fun h1 ↦ phi_halts_mono e s t n h h1

/- The least stage s at which ϕₑ,ₛ(n)↓ (if it exists) -/
def runtime (e n : ℕ) : Part ℕ :=
  rfind (fun s => (Phi_s e (s) n).isSome)

/- TODO: runtime lemmas can be cleaned up with Nat.rfind spec/min? -/
/- Runtime r is minimal - if s < r, then ϕₑ,ₛ(n)↑ -/
lemma runtime_is_min (e r n : ℕ) : (r ∈ (runtime e n)) ↔
    Phi_s_halts e r n ∧ (∀ (t : ℕ), t < r → Phi_s_diverges e t n) := by
  constructor
  · intro h
    simp [runtime] at h
    obtain ⟨hs, hs2⟩ := h
    unfold Phi_s_halts
    constructor
    · simp_all [Option.isSome_iff_exists]
    · simp_all [Phi_s_diverges, Phi_s_halts]
  · intro ⟨h1, h2⟩
    apply Option.isSome_iff_exists.mpr at h1
    simp [runtime]
    constructor
    · exact h1
    · intro m hm
      apply h2 at hm
      unfold Phi_s_diverges Phi_s_halts at hm
      push_neg at hm
      exact Option.eq_none_iff_forall_ne_some.mpr hm

lemma runtime_is_min' (e s n : ℕ) (h : Phi_s_halts e s n) :
    ∃ r ∈ runtime e n, r ≤ s := by
  apply Nat.rfind_min'
  exact Option.isSome_iff_exists.mpr h

/- TODO : provide an explicit version and an exists version? -/
/- ϕₑ(n)↓ iff there is a stage s at which ϕₑ,ₛ(n)↓ -/
lemma phi_halts_stage_exists (e n : ℕ) : Phi_halts e n ↔ ∃ s, Phi_s_halts e s n := by
  unfold Phi_s_halts Phi_halts Phi_s Phi
  simp [evaln_complete]
  constructor
  · intro ⟨x, ⟨k, h⟩⟩
    use e+x+k+1 -- one plus the maximum of e, x, and k would work, but this is easier
    constructor
    · constructor
      · linarith -- e < e+x+k+1
      · use x
        constructor
        · linarith -- x < e+x+k+1
        · apply evaln_mono
          rotate_left
          · exact h
          · linarith
    · use x
      apply evaln_mono
      rotate_left
      · exact h
      · linarith -- k < e+x+k+1
  · intro ⟨s, ⟨⟨_, ⟨_, ⟨_, _⟩⟩⟩, ⟨x, _⟩⟩⟩
    use x
    use s

/- ϕₑ(n)↓ iff there is a *least* stage s at which ϕₑ,ₛ(n)↓ -/
lemma phi_halts_runtime_exists (e n : ℕ) : Phi_halts e n ↔ ∃ r, r ∈ runtime e n := by
  constructor
  · intro h
    rw [phi_halts_stage_exists] at h
    obtain ⟨s, h⟩ := h
    have h1 : ∃ r, r ∈ rfindOpt (λ s => Phi_s e s n) := by
      rw [← Part.dom_iff_mem, rfindOpt_dom]
      use s
      exact h
    obtain ⟨y, h1⟩:= h1
    simp [rfindOpt] at h1
    obtain ⟨t, ⟨h2, h1⟩⟩ := h1
    have h4 : ∃ y, Phi_s e t n = some y := ⟨y, h1⟩
    apply halt_stage_gt_zero at h4
    rw [gt_iff_lt, lt_iff_add_one_le, zero_add] at h4
    use t
    simp_all [runtime]
  · intro ⟨r, h⟩
    rw [runtime_is_min] at h
    rw [phi_halts_stage_exists]
    use r
    exact h.left

/- ϕₑ,ₛ(n)↓ iff n ∈ Wₑ,ₛ -/
lemma W_s_Phi_s (e s n : ℕ) : n ∈ W_s e s ↔ Phi_s_halts e s n := by
unfold W_s Phi_s_halts
simp
intro x h
apply halt_input_bound e s n
unfold Phi_s_halts
use x
exact h

lemma Ws_gt_zero (e s n : ℕ) : n ∈ W_s e s → s > 0 := by
  rw [W_s_Phi_s]
  apply halt_stage_gt_zero

lemma Ws_zero_empty (e : ℕ) : W_s e 0 = ∅ := by
  ext n
  rw [W_s_Phi_s]
  simp
  exact stage_zero_diverges e n

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

/- Membership in some W_{e,s} implies runtime r exists, and membership in W_{e, r+1}-/
lemma Ws_runtime (e s n : ℕ) (h : n ∈ W_s e s) : ∃ r, r ∈ runtime e n ∧ n ∈ W_s e r := by
  simp [W_s] at h
  obtain ⟨h, h1⟩ := h
  have h2 : ∃ s, Phi_s_halts e s n := by exact Exists.intro s h1
  rw [← phi_halts_stage_exists, phi_halts_runtime_exists] at h2
  obtain ⟨r, h2⟩ := h2
  use r
  constructor
  · exact h2
  · simp [W_s]
    rw [runtime_is_min] at h2
    obtain ⟨h2, h3⟩ := h2
    constructor
    · apply halt_input_bound at h2
      linarith
    · exact h2

/- Wₑ,ₛ ⊆ Wₑ  -/
lemma W_s_subset_W (e s : ℕ) : (W_s e s).toSet ⊆ W e := by
  intro x
  simp [W_s, W]
  intro h h1
  rw [← Phi_halts, phi_halts_stage_exists]
  use s

/- Wₑ = ⋃ₛ Wₑ,ₛ -/
lemma W_mem_iff_W_s (e n: ℕ) : n ∈ W e ↔ ∃ s, n ∈ W_s e s :=by
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

lemma W_eq_union_W_s (e : ℕ) : W e = ⋃ (s : ℕ), W_s e s := by
ext x
rw [W_mem_iff_W_s]
simp
