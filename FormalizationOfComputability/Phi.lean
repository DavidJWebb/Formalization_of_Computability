/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.Sets
import Mathlib.Tactic.Linarith

/-
# ϕₑ and Wₑ
This file contains the definitions most commonly used by working computability theorists:
the use functions ϕₑ, the enumerable sets Wₑ, and their coputable
approximations ϕ_{e, s} and W_{e, s}.

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


/-- ϕₑ,ₛ(n) is decidable -/
instance (e s n : ℕ): Decidable (Phi_s_halts e s n) := by
  unfold Phi_s_halts Phi_s
  simp
  have h : Decidable (∃ x, evaln s (ofNatCode e) n = some x) := by
     match evaln s (ofNatCode e) n with
    | some x        => exact isTrue ⟨x, rfl⟩
    | Option.none   => exact isFalse (λ ⟨x, h⟩ => Option.noConfusion h)
  apply instDecidableAnd

/-- Wₑ,ₛ = the domain of ϕₑ,ₛ. As all inputs n ≥ s do not halt,
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
  have h4 : y = z := by
    simp [h] at h3
    exact h3
  rw [h4]
  exact h2

/- If ϕₑ,ₛ(n)↓, then e < s -/
lemma halt_index_bound (e s n : ℕ) (h : Phi_s_halts e s n) :
    e < s := by
  simp [Phi_s_halts, Phi_s] at h
  exact h.left.left

/- A helper lemma - if ϕₑ,ₛ(n)↓, then s > 0 -/
lemma halt_stage_gt_zero (e s n : ℕ) (h : Phi_s_halts e s n) : s > 0 := by
  contrapose h
  simp at h
  unfold Phi_s_halts Phi_s
  rw [h]
  simp

open Primrec


lemma primrec_filter (A : ℕ → Prop) (hf : DecidablePred A) (hf1 : PrimrecPred A) :
    Primrec λ n => ((List.range (n)).filter (fun y => A y)) := by
  -- the function (n => the list of values y < n such that A y) is primitive recursive
  let f : ℕ → List ℕ := λ n => List.range n
  let g : ℕ → ℕ → Option Nat := λ x => (λ y => (if A y = True then y else Option.none))
  have h1 : Primrec fun (n : ℕ) => List.filterMap (g n) (f n) := by
    apply listFilterMap
    · exact list_range
    · unfold g
      apply Primrec.ite
      · simp
        refine PrimrecPred.comp hf1 ?_
        exact snd
      · refine option_some_iff.mpr ?_
        exact snd
      · exact Primrec.const Option.none
  -- this filter map sends n to [0,...,n-1], then for each x in that list, keeps x iff A x
  have h2 : ∀ n, ∀ i, i ∈ List.filterMap (g n) (f n) ↔
                      i ∈ (List.range (n)).filter (fun y => A y) := by
    simp [f, g]
  have h3 : ∀ n, List.Sorted (· < ·) (List.filterMap (g n) (f n)) := by
    intro n
    simp [f, g]
    sorry

  have h4 : ∀ n, List.Sorted (· < ·) ((List.range (n)).filter (fun y => A y)) := by
    intro n
    exact List.Sorted.filter (fun y ↦ decide (A y)) (List.sorted_lt_range n)

  have h5 : ∀ n, List.filterMap (g n) (f n) = (List.range (n)).filter (fun y => A y) := by
    intro n
    sorry

  have h6 : (fun n => (List.range (n)).filter (fun y => A y)) =
            (fun n => List.filterMap (g n) (f n)) := by
    symm
    exact (Set.eqOn_univ (fun n ↦ List.filterMap (g n) (f n)) fun n ↦
          List.filter (fun y ↦ decide (A y)) (List.range n)).mp
          fun ⦃x⦄ a ↦ h5 x
  rw [h6]
  exact h1




/-- ϕₑ,ₛ is a primitive recursive function -/
lemma phi_s_primrec (e s : ℕ) : Primrec (Phi_s e s) := by
  unfold Phi_s
  have h : Primrec fun (((s, e),n) : (ℕ × ℕ) × ℕ) => evaln s (ofNatCode e) n := by
      exact primrec_evaln
  have h1 : Primrec (evaln s (ofNatCode e)) := by
    exact h.comp (Primrec.pair (Primrec.pair (Primrec.const s) (Primrec.const e))
    Primrec.id)
  refine Primrec.ite ?_ ?_ ?_
  · refine PrimrecPred.and ?_ ?_
    · refine PrimrecRel.comp ?_ ?_ ?_
      · exact Primrec.nat_lt
      · exact Primrec.const e
      · exact Primrec.const s
    · unfold PrimrecPred
  · exact h1
  · exact Primrec.const Option.none

/- ϕₑ is a partial computable function -/
theorem phi_partrec (e : ℕ) : Nat.Partrec (Phi e) := by
  unfold Phi
  rw [Code.exists_code]
  use ofNatCode e


/-- The Wₑ,ₛ are Δ01-/
lemma W_s_Delta01 (e s : ℕ) : Delta01 (W_s e s) := by
  simp [Delta01, computable_set, W_s]
  use Phi_s_halts e s
  constructor
  · apply Primrec.to_comp
    simp [Phi_s_halts]
    have h : ∀ b, ((∃ x, x ∈ Phi_s e s b) ↔ (∃ x < s, x ∈ Phi_s e s b)) := by
      intro b
      constructor
      · intro ⟨x, h⟩
        use x
        constructor
        · apply halt_output_bound e s b
          exact h
        · exact h
      · intro ⟨x, h⟩
        use x
        exact h.right
    · have h1 := phi_s_primrec e s
      sorry
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
  · intro h
    obtain ⟨e, h⟩ := h
    rw [h]
    exact W_Sigma01 e

/- Monotonicity of halting: if s < t and ϕ_{e,s}(n)↓, then ϕ_{e,t}(n)↓ -/
lemma phi_halts_mono (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_s_halts e s n) :
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
  rfindOpt (fun s => if (Phi_s e (s) n).isSome then some s else Option.none)

/- Statements involving runtime can appear to have off-by-one errors.
This is because if x has runtime s, x ∉ W_{e,s} but instead x ∈ W_{e, s+1}. -/

/- Runtime r is minimal - if s < r, then ϕₑ,ₛ(n)↑ -/
lemma runtime_is_min (e r n : ℕ) : (r ∈ (runtime e n)) ↔
    Phi_s_halts e (r) n ∧ (∀ (t : ℕ), t < r → Phi_s_diverges e t n) := by
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
  · intro ⟨s, ⟨⟨h, ⟨y, ⟨hys, h1⟩⟩⟩, ⟨x, h2⟩⟩⟩
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
    obtain ⟨t, ⟨⟨h2, h3⟩, h1⟩⟩ := h1
    have h4 : ∃ y, Phi_s e t n = some y := ⟨y, h1⟩
    apply halt_stage_gt_zero at h4
    rw [gt_iff_lt, lt_iff_add_one_le, zero_add] at h4
    use t
    simp [runtime, rfindOpt]
    constructor
    · constructor
      · exact h2
      · intros s h5
        apply h3 at h5
        exact h5
    · exact h2
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

/- Membership in some W_{e,s} implies runtime t exists, and membership in W_{e, t}-/
lemma Ws_runtime (e s n : ℕ) (h : n ∈ W_s e s) : ∃ r, r ∈ runtime e n ∧ n ∈ W_s e (r+1) := by
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
    · apply phi_halts_mono e r (r+1) n
      · linarith
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
