/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.Sets
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.Linarith
/-
# ϕₑ and Wₑ
This file contains the definitions most commonly used by working computability theorists:
the use functions ϕₑ, the enumerable sets Wₑ, and their computable
approximations ϕ_{e, s} and W_{e, s}.

In some sense Phi_s and Phi are merely wrappers for evaln and eval, respectively,
modified to match common computability theory notation.

## Main results

## Notation
- 'Delta01' is used to mean a set is computable
- 'Sigma01' is used to mean a set is partial computable
## References
- [R. I. Soare *Turing Computability - Theory and Applications*] [Soare2016]
-/


namespace Computability

abbrev Delta01 := Computable.set
abbrev Sigma01 := Partrec.set

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
      simp [encodeCode, ofNatCode, ← ihf, ← ihg]
  | comp cf cg ihf ihg =>
      simp [encodeCode, ofNatCode, ← ihf, ← ihg]
  | prec cf cg ihf ihg =>
      simp [encodeCode, ofNatCode, ← ihf, ← ihg]
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
    conv_rhs => rw [← bit_bodd_div2 n, ← bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_5]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, IH, IH1, IH2, bit_val]

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
@[grind, simp]
def Phi_s_halts (e s n : ℕ) : Prop :=
    ∃ x, x ∈ Phi_s e s n

/- ϕₑ(n)↓ iff it has an output -/
@[grind, simp]
def Phi_halts (e n : ℕ) : Prop :=
    ∃ x, x ∈ Phi e n

private lemma helperlemma (x : ℕ) : Option.none = some x → False := by
    intro h
    simp_all only [reduceCtorEq]

instance (e s n : ℕ) : Decidable (∃ x, x ∈ Phi_s e s n) := by
  simp only [Phi_s, Option.mem_def, Option.ite_none_right_eq_some, exists_and_left]
  have h : Decidable (∃ x, evaln s (ofNatCode e) n = some x) := by
     match evaln s (ofNatCode e) n with
    | some x        => exact isTrue ⟨x, rfl⟩
    | Option.none   => exact isFalse (λ ⟨x, h⟩ => (helperlemma x h))
  exact instDecidableAnd

/- ϕₑ,ₛ(n) is decidable -/
instance (e s n : ℕ) : Decidable (Phi_s_halts e s n) := by
  simp only [Phi_s_halts, Phi_s, Option.mem_def, Option.ite_none_right_eq_some, exists_and_left]
  have h : Decidable (∃ x, evaln s (ofNatCode e) n = some x) := by
     match evaln s (ofNatCode e) n with
    | some x        => exact isTrue ⟨x, rfl⟩
    | Option.none   => exact isFalse (λ ⟨x, h⟩ => (helperlemma x h))
  exact instDecidableAnd

/- Wₑ,ₛ = the domain of ϕₑ,ₛ. As all inputs n ≥ s do not halt, this set is necessarily finite. -/
@[grind, simp]
def W_s (e s : ℕ): Finset ℕ :=
  (Finset.range s).filter (Phi_s_halts e s)

/- Wₑ = {n | ϕₑ(n)↓} -/
@[grind, simp]
def W (e : ℕ) : Set ℕ := (Phi e).Dom

variable {e s t n x y : ℕ} {X : Set ℕ}

/- If ϕₑ,ₛ(n)↓, then n < s -/
@[grind →, simp]
lemma halt_input_bound (h : Phi_s_halts e s n) : n < s := by
  simp only [Phi_s_halts, Phi_s, Option.mem_def, Option.ite_none_right_eq_some,
    exists_and_left] at h
  obtain ⟨x, hx⟩ := h.right
  exact Code.evaln_bound hx

/- If ϕₑ,ₛ(n) = y, then y < s -/
@[grind →, simp]
lemma halt_output_bound (h : y ∈ (Phi_s e s n)) : y < s := by
  simp only [Phi_s, Option.mem_def, Option.ite_none_right_eq_some] at h
  grind

/- If ϕₑ,ₛ(n)↓, then e < s -/
@[grind →, simp]
lemma halt_index_bound (h : Phi_s_halts e s n) : e < s := by grind [Phi_s_halts, Phi_s]

/- Helper lemmas - ϕ_{e, 0}(n)↑ -/
@[grind →, simp]
lemma halt_stage_gt_zero (h : Phi_s_halts e s n) : s > 0 := by grind [Phi_s_halts, Phi_s]

@[grind ., simp]
lemma stage_zero_diverges : ¬ Phi_s_halts e 0 n := by grind [Phi_s_halts, Phi_s]

open Primrec

-- a helper lemma for showing that phi_s is primitive recursive
private lemma bounded_exists (f : ℕ → ℕ → Prop) (s : ℕ) [DecidableRel f]
    (hf : PrimrecRel f) :
      PrimrecPred (λ n => ∃ y < s, (f y n)) := by
    have h := PrimrecRel.exists_mem_list hf
    unfold PrimrecRel at h
    have hpair : Primrec (λ n : ℕ => (List.range s, n)) :=
      (Primrec.const (List.range s)).pair Primrec.id
    have h3 := h.comp hpair
    simp_all only [List.mem_range]

/- ϕₑ,ₛ is a primitive recursive function -/
lemma phi_s_primrec : Primrec (Phi_s e s) := by
  have h := primrec_evaln.comp (pair (pair (const s) (const (ofNatCode e))) .id)
  apply ite (PrimrecPred.and (PrimrecRel.comp nat_lt (const e) (const s)) ?_) h (const Option.none)
  apply bounded_exists
  simp only [PrimrecRel, Option.mem_def]
  exact PrimrecRel.comp Primrec.eq (.comp h snd) (option_some_iff.mpr fst)

lemma phi_s_halts_primrec : PrimrecPred (Phi_s_halts e s) := by
  have h (n : ℕ) : (∃ x, Phi_s e s n = some x) ↔ (∃ x < s, Phi_s e s n = some x) := by
    constructor
    · intro ⟨x, h⟩
      use x
      constructor
      · exact halt_output_bound h
      · exact h
    · simp_all
  unfold Phi_s_halts
  simp only [Option.mem_def, h]
  apply bounded_exists
  apply PrimrecRel.comp₂ Primrec.eq (comp₂ (phi_s_primrec) (Primrec₂.right))
  exact comp₂ option_some Primrec₂.left

/- ϕₑ is a partial computable function -/
theorem phi_partrec : Nat.Partrec (Phi e) := by
  unfold Phi
  rw [Code.exists_code]
  use ofNatCode e

/- The Wₑ,ₛ are primitive recursive-/
lemma W_s_Primrec : Primrec.set (W_s e s) := by
  simp only [Primrec.set, W_s, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
  use Phi_s_halts e s
  constructor
  · exact Primrec.ite (phi_s_halts_primrec) (const true) (const false)
  · grind

/- The Wₑ are Σ01 -/
lemma W_Sigma01 (e : ℕ) : Sigma01 (W e) := by
  use λ n ↦ (Phi e n).map (λ _ => ())
  constructor
  · refine Partrec.map ?_ (Primrec₂.to_comp (Primrec₂.const ()))
    constructor
    · exact phi_partrec
    · exact Partrec.nat_iff.mp (Computable.partrec Computable.id)
  · rfl

/- Sigma01 sets can be written as Wₑ -/
lemma Sigma01_is_W (h : Sigma01 X) : ∃ e, X = W e := by
· obtain ⟨f, ⟨h1, h2⟩⟩ := h
  let f_nat : ℕ →. ℕ := λ n => (f n).map (λ _ => 1)
  have h3 := Partrec.nat_iff.mp (Partrec.map h1 (Primrec₂.to_comp (Primrec₂.const 1)))
  have h4 : f.Dom = f_nat.Dom := rfl
  rw [Code.exists_code] at h3
  obtain ⟨c, h3⟩ := h3
  rw [← h2, h4]
  use c.encodeCode
  unfold W Phi
  rw [← ofNatCode_encode c]
  exact congrArg PFun.Dom (id (Eq.symm h3))

/- The Σ01 sets are exactly the Wₑ -/
lemma Sigma01_iff_W : Sigma01 X ↔ ∃ e, X = W e := by grind [Sigma01_is_W, W_Sigma01]

/- Monotonicity of halting: if s < t and ϕ_{e,s}(n)↓, then ϕ_{e,t}(n)↓ -/
@[grind →, simp]
lemma phi_halts_mono (h : s ≤ t) (h1 : Phi_s_halts e s n) : Phi_s_halts e t n := by
  revert h1
  simp only [Phi_s_halts, Phi_s, Option.mem_def, Option.ite_none_right_eq_some, exists_and_left,
    and_imp, forall_exists_index]
  intro _ x _ h3 _ _
  constructor
  · constructor
    · linarith
    · use x
      constructor
      · linarith
      · exact evaln_mono h h3
  · exact ⟨x, evaln_mono h h3⟩

/- Reverse monotonicity of halting: if s < t and ϕ_{e,t}(n)↑, then ϕ_{e,s}(n)↑ -/
@[grind →, simp]
lemma phi_halts_mono_reverse (h : s ≤ t) (h1 : ¬ Phi_s_halts e t n) : ¬ Phi_s_halts e s n := by
  grind

/- The least stage s at which ϕₑ,ₛ(n)↓ (if it exists) -/
@[grind, simp]
def runtime (e n : ℕ) : Part ℕ :=
  rfind (fun s => (Phi_s e (s) n).isSome)

/- TODO: runtime lemmas can be cleaned up with Nat.rfind spec/min? -/
/- Runtime r is minimal - if s < r, then ϕₑ,ₛ(n)↑ -/
@[grind =, simp]
lemma runtime_is_min (r : ℕ) : (r ∈ (runtime e n)) ↔
    Phi_s_halts e r n ∧ (∀ (t : ℕ), t < r → ¬ Phi_s_halts e t n) := by
  constructor
  · intro h
    simp only [runtime, Part.coe_some, mem_rfind, Part.mem_some_iff, Bool.true_eq, Bool.false_eq,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    constructor
    <;> simp_all [Option.isSome_iff_exists, Phi_s_halts]
  · intro ⟨h1, h2⟩
    apply Option.isSome_iff_exists.mpr at h1
    simp only [runtime, Part.coe_some, mem_rfind, Part.mem_some_iff, Bool.true_eq, Bool.false_eq,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    constructor
    · exact h1
    · intro m hm
      apply h2 at hm
      unfold Phi_s_halts at hm
      push_neg at hm
      exact Option.eq_none_iff_forall_ne_some.mpr hm

@[grind ., simp]
lemma runtime_is_min' (h : Phi_s_halts e s n) :
    ∃ r ∈ runtime e n, r ≤ s := Nat.rfind_min' (Option.isSome_iff_exists.mpr h)

/- TODO : provide an explicit version and an exists version? -/
/- ϕₑ(n)↓ iff there is a stage s at which ϕₑ,ₛ(n)↓ -/
@[grind =, simp]
lemma phi_halts_stage_exists : Phi_halts e n ↔ ∃ s, Phi_s_halts e s n := by
  unfold Phi_s_halts Phi_halts Phi_s Phi
  simp only [evaln_complete, Option.mem_def, Option.ite_none_right_eq_some, exists_and_left]
  constructor
  · intro ⟨x, ⟨k, h⟩⟩
    use e+x+k+1 -- one plus the maximum of e, x, and k would also work
    constructor
    · constructor
      · linarith -- e < e+x+k+1
      · use x
        constructor
        · linarith -- x < e+x+k+1
        · apply evaln_mono
          · linarith
          · exact h
    · use x
      apply evaln_mono
      · linarith -- k < e+x+k+1
      · exact h
  · grind

/- ϕₑ(n)↓ iff there is a *least* stage s at which ϕₑ,ₛ(n)↓ -/
@[grind =, simp]
lemma phi_halts_runtime_exists : Phi_halts e n ↔ ∃ r, r ∈ runtime e n := by
  constructor
  · intro h
    rw [phi_halts_stage_exists] at h
    obtain ⟨s, h⟩ := h
    have h1 : ∃ r, r ∈ rfindOpt (λ s => Phi_s e s n) := by
      rw [← Part.dom_iff_mem, rfindOpt_dom]
      exact ⟨s, h⟩
    obtain ⟨y, h1⟩ := h1
    simp only [rfindOpt, Part.coe_some, Part.mem_bind_iff, mem_rfind, Part.mem_some_iff,
      Bool.true_eq, Bool.false_eq, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      Part.mem_ofOption, Option.mem_def] at h1
    obtain ⟨t, ⟨_, h1⟩⟩ := h1
    have h4 : ∃ y, Phi_s e t n = some y := ⟨y, h1⟩
    apply halt_stage_gt_zero at h4
    rw [gt_iff_lt, lt_iff_add_one_le, zero_add] at h4
    use t
    simp_all [runtime]
  · intro ⟨r, h⟩
    rw [runtime_is_min] at h
    rw [phi_halts_stage_exists]
    exact ⟨r, h.left⟩

/- ϕₑ,ₛ(n)↓ iff n ∈ Wₑ,ₛ -/
@[simp]
lemma W_s_Phi_s : n ∈ W_s e s ↔ Phi_s_halts e s n := by
  unfold W_s Phi_s_halts
  simp only [Option.mem_def, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp,
    forall_exists_index]
  intro x h
  exact halt_input_bound ⟨x, h⟩

@[simp]
lemma Ws_gt_zero : n ∈ W_s e s → s > 0 := by grind

@[simp]
lemma Ws_zero_empty : W_s e 0 = ∅ := by grind

/- ϕₑ(x)↓ ↔ x ∈ Wₑ -/
@[simp]
lemma mem_W_phi : n ∈ W e ↔ Phi_halts e n := Part.dom_iff_mem

/- W_{s} ⊆ W_{e, s+1}  -/
@[simp]
lemma W_s_mono (h : s ≤ t) : (W_s e s) ⊆ (W_s e t) := by grind

/- Membership in some W_{e,s} implies runtime r exists, and membership in W_{e, r+1}-/
@[grind ., simp]
lemma Ws_runtime (h : n ∈ W_s e s) : ∃ r, r ∈ runtime e n ∧ n ∈ W_s e r := by grind

/- Wₑ,ₛ ⊆ Wₑ  -/
@[grind! ., simp]
lemma W_s_subset_W : ↑(W_s e s) ⊆ W e := by
  intro x h
  rw [mem_W_phi]
  simp only [W_s, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at h
  rw [phi_halts_stage_exists]
  use s
  exact h.right

/- Wₑ = ⋃ₛ Wₑ,ₛ -/
@[grind =, simp]
lemma W_mem_iff_W_s : n ∈ W e ↔ ∃ s, n ∈ W_s e s := by
  constructor
  · intro h
    apply Part.dom_iff_mem.mp at h
    rw [← Phi_halts, phi_halts_stage_exists] at h
    obtain ⟨s, h⟩ := h
    simp only [W_s_Phi_s]
    exact ⟨s, h⟩
  · grind

lemma W_eq_union_W_s : W e = ⋃ (s : ℕ), W_s e s := by
  ext x
  rw [W_mem_iff_W_s]
  simp
