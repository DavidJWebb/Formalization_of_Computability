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

In some sense ϕ_s and ϕ are merely wrappers for evaln and eval, respectively,
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

private lemma helperlemma (x : ℕ) : Option.none = some x → False := by
    intro h
    simp_all only [reduceCtorEq]

variable {e s t n x y : ℕ} {X : Set ℕ}


/- ϕₑ,ₛ(n), the eth Turing program evaluated for s steps on input n.
Following Soare, we require the index, input, and output to be less than s -/
def ϕ_s (e s n : ℕ) : Option ℕ :=
    if (e < s) ∧ (∃ y < s, y ∈ evaln s (ofNatCode e) n)
    then evaln s (ofNatCode e) n
    else Option.none

/- ϕₑ(n), the eth Turing program evaluated on input n -/
def ϕ (e : ℕ) : ℕ →. ℕ := eval (ofNatCode e)

/- ϕₑ,ₛ(n)↓ iff it has an output -/
@[grind, simp]
def ϕ_s_halts (e s n : ℕ) : Prop := (ϕ_s e s n).isSome

/- ϕₑ(n)↓ iff it has an output -/
@[grind, simp]
def ϕ_halts (e n : ℕ) : Prop := (ϕ e n).Dom

/- If ϕₑ,ₛ(n)↓, then ϕₑ(n)↓ -/
lemma ϕ_sound (h : ϕ_s_halts e s n) : ϕ_halts e n := by
  have h1 : ∃ s, ϕ_s_halts e s n := by exact ⟨s, h⟩
  revert h1
  unfold ϕ_s_halts ϕ_s
  unfold ϕ_halts ϕ
  simp only [Part.dom_iff_mem, evaln_complete]
  grind

/- ϕₑ(n)↓ iff there is a stage s at which ϕₑ,ₛ(n)↓ -/
@[grind =, simp]
lemma ϕ_complete : ϕ_halts e n ↔ ∃ s, ϕ_s_halts e s n := by
  constructor
  · unfold ϕ_s_halts ϕ_halts ϕ_s ϕ
    simp only [Part.dom_iff_mem, evaln_complete, Option.mem_def, Option.isSome_iff_exists,
    Option.ite_none_right_eq_some, exists_and_left]
    intro ⟨x, ⟨k, h⟩⟩
    let N := e + x + k + 1 -- one plus the maximum of e, x, and k would also work
    have he : e < N := by omega
    have hx : x < N := by omega
    have hk : k < N := by omega
    use N
    simp only [he, true_and]
    refine exists_and_exists_comm.mpr ?_
    use x
    use x
    simp only [hx, true_and, and_self]
    exact evaln_mono (le_of_succ_le hk) h
  · intro ⟨s, h⟩
    exact ϕ_sound h

/- If ϕₑ,ₛ(n)↓, then n < s -/
@[grind →, simp]
lemma ϕ_input_bound (h : ϕ_s_halts e s n) : n < s := by
  simp only [ϕ_s_halts, ϕ_s, Option.mem_def, Option.isSome_iff_exists,
    Option.ite_none_right_eq_some, exists_and_left] at h
  obtain ⟨x, hx⟩ := h.right
  exact Code.evaln_bound hx

/- If ϕₑ,ₛ(n) = y, then y < s -/
@[grind →, simp]
lemma ϕ_output_bound (h : y ∈ (ϕ_s e s n)) : y < s := by
  simp only [ϕ_s, Option.mem_def, Option.ite_none_right_eq_some] at h
  grind

/- If ϕₑ,ₛ(n)↓, then e < s -/
@[grind →, simp]
lemma ϕ_index_bound (h : ϕ_s_halts e s n) : e < s := by grind [ϕ_s_halts, ϕ_s]

/- Helper lemmas - ϕ_{e, 0}(n)↑ -/
@[grind →, simp]
lemma halt_stage_gt_zero (h : ϕ_s_halts e s n) : s > 0 := by grind [ϕ_s_halts, ϕ_s]

@[grind ., simp]
lemma stage_zero_diverges : ¬ ϕ_s_halts e 0 n := by grind [ϕ_s_halts, ϕ_s]

open Primrec

-- a helper lemma for showing that ϕ_s is primitive recursive
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
lemma ϕ_s_primrec : Primrec (ϕ_s e s) := by
  have h := primrec_evaln.comp (pair (pair (const s) (const (ofNatCode e))) .id)
  apply ite (PrimrecPred.and (PrimrecRel.comp nat_lt (const e) (const s)) ?_) h (const Option.none)
  apply bounded_exists
  simp only [PrimrecRel, Option.mem_def]
  exact PrimrecRel.comp Primrec.eq (.comp h snd) (option_some_iff.mpr fst)

/- ϕ_s_halts is a primitive recursive predicate -/
lemma ϕ_s_halts_primrec : PrimrecPred (ϕ_s_halts e s) := by
  have h (n : ℕ) : (∃ x, ϕ_s e s n = some x) ↔ (∃ x < s, ϕ_s e s n = some x) := by
    constructor
    · intro ⟨x, h⟩
      use x
      simp only [ϕ_output_bound h, h, and_self]
    · simp_all
  unfold ϕ_s_halts
  simp only [Option.isSome_iff_exists, h]
  apply bounded_exists
  apply PrimrecRel.comp₂ Primrec.eq (comp₂ (ϕ_s_primrec) (Primrec₂.right))
  exact comp₂ option_some Primrec₂.left

/- ϕₑ,ₛ(n) is decidable -/
instance (e s n : ℕ) : Decidable (ϕ_s e s n).isSome :=
  (ϕ_s e s n).isSome.decEq true

/- ϕₑ,ₛ(n) is decidable -/
instance (e s n : ℕ) : Decidable (ϕ_s_halts e s n) :=
  instDecidableEqBoolIsSomeNatϕ_sTrue e s n

/- ϕₑ is a partial computable function -/
theorem ϕ_partrec : Nat.Partrec (ϕ e) := by
  unfold ϕ
  rw [Code.exists_code]
  use ofNatCode e

/- Monotonicity of halting: if s < t and ϕ_{e,s}(n)↓, then ϕ_{e,t}(n)↓ -/
@[grind →, simp]
lemma ϕ_halts_mono (h : s ≤ t) (h1 : ϕ_s_halts e s n) : ϕ_s_halts e t n := by
  revert h1
  simp only [ϕ_s_halts, ϕ_s, Option.mem_def, Option.isSome_iff_exists,
    Option.ite_none_right_eq_some, exists_and_left, and_imp, forall_exists_index]
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
lemma ϕ_halts_mono_reverse (h : s ≤ t) (h1 : ¬ ϕ_s_halts e t n) : ¬ ϕ_s_halts e s n := by
  grind

/- The least stage s at which ϕₑ,ₛ(n)↓ (if it exists) -/
@[grind, simp]
def runtime (e n : ℕ) : Part ℕ := rfind (fun s => (ϕ_s e s n).isSome)

/- TODO: runtime lemmas can be cleaned up with Nat.rfind spec/min? -/
/- Runtime r is minimal - if s < r, then ϕₑ,ₛ(n)↑ -/
@[simp]
lemma runtime_spec (r : ℕ) (h : r ∈ runtime e n) : ϕ_s_halts e r n := by
  simp_all only [runtime, Part.coe_some, mem_rfind, Part.mem_some_iff, Bool.true_eq, Bool.false_eq,
  Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, ϕ_s_halts]

lemma runtime_min (r : ℕ) (h : r ∈ (runtime e n)) : ∀ t, t < r → ¬ ϕ_s_halts e t n := by
  simp_all

/- ϕₑ(n)↓ iff there is a *least* stage s at which ϕₑ,ₛ(n)↓ -/
@[grind =, simp]
lemma ϕ_halts_runtime_exists : ϕ_halts e n ↔ ∃ r, r ∈ runtime e n := by
  constructor
  · intro h
    rcases (ϕ_complete.mp h) with ⟨s, hs⟩
    have h1 : (runtime e n).Dom := by
      unfold runtime
      use s
      simp only [Part.coe_some, Part.mem_some_iff, Bool.true_eq, Part.some_dom,
        implies_true, and_true]
      exact hs
    simpa [Part.dom_iff_mem] using h1
  · intro ⟨r, h⟩
    apply ϕ_complete.mpr
    apply runtime_spec at h
    exact ⟨r, h⟩

/- Wₑ,ₛ = the domain of ϕₑ,ₛ, i.e. elements entering before stage s.
As all inputs n ≥ s do not halt, this set is necessarily finite. -/
@[grind, simp]
def W_s (e s : ℕ): Finset ℕ := (Finset.range s).filter (ϕ_s_halts e s)

/- Wₑ = {n | ϕₑ(n)↓} -/
@[grind, simp]
def W (e : ℕ) : Set ℕ := (ϕ e).Dom

instance (e s n : ℕ) : Decidable (n ∈ W_s e s) :=
  Finset.decidableMem n (Finset.filter (ϕ_s_halts e s) (Finset.range s))

/- The Wₑ,ₛ are primitive recursive-/
lemma W_s_Primrec : Primrec.set (W_s e s) := by
  simp only [Primrec.set, W_s, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
  use ϕ_s_halts e s
  constructor
  · exact Primrec.ite (ϕ_s_halts_primrec) (const true) (const false)
  · grind

/- The Wₑ are Σ01 -/
lemma W_Sigma01 (e : ℕ) : Sigma01 (W e) := by
  use λ n ↦ (ϕ e n).map (λ _ => ())
  constructor
  · refine Partrec.map ?_ (Primrec₂.to_comp (Primrec₂.const ()))
    constructor
    · exact ϕ_partrec
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
  unfold W ϕ
  rw [← ofNatCode_encode c]
  exact congrArg PFun.Dom (id (Eq.symm h3))

/- The Σ01 sets are exactly the Wₑ -/
lemma Sigma01_iff_W : Sigma01 X ↔ ∃ e, X = W e := by grind [Sigma01_is_W, W_Sigma01]

/- ϕₑ,ₛ(n)↓ iff n ∈ Wₑ,ₛ -/
@[simp]
lemma W_s_ϕ_s : n ∈ W_s e s ↔ ϕ_s_halts e s n := by
  simp_all only [W_s, Finset.mem_filter, Finset.mem_range, ϕ_s_halts, and_iff_right_iff_imp]
  exact fun a ↦ ϕ_input_bound a

@[simp]
lemma Ws_gt_zero : n ∈ W_s e s → s > 0 := by grind

@[simp]
lemma Ws_zero_empty : W_s e 0 = ∅ := by grind

/- ϕₑ(x)↓ ↔ x ∈ Wₑ -/
@[simp]
lemma mem_W_ϕ : n ∈ W e ↔ ϕ_halts e n := by exact Eq.to_iff rfl

/- Monotonicity of W_s: W_s ⊆ W_{e, s+1}  -/
@[simp]
lemma W_s_mono (h : s ≤ t) : (W_s e s) ⊆ (W_s e t) := by grind

/- Reverse monotonicity of W_s-/
@[simp]
lemma W_s_mono_reverse (h : s ≤ t) (hx : x ∉ W_s e t) : x ∉ W_s e s := by grind

/- Membership in some W_{e,s} implies runtime r exists, and membership in W_{e, r}-/
@[grind ., simp]
lemma Ws_runtime (h : n ∈ W_s e s) : ∃ r, r ∈ runtime e n ∧ n ∈ W_s e r := by
  have ⟨r, h1⟩ := ϕ_halts_runtime_exists.mp (ϕ_complete.mpr ⟨s, W_s_ϕ_s.mp h⟩)
  refine ⟨r, ⟨h1, W_s_ϕ_s.mpr ?_⟩⟩
  apply runtime_spec at h1
  exact h1

/- Wₑ,ₛ ⊆ Wₑ  -/
@[grind! ., simp]
lemma W_s_subset_W : ↑(W_s e s) ⊆ W e := by
  intro x h
  rw [mem_W_ϕ]
  simp only [W_s, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at h
  rw [ϕ_complete]
  grind

/- Wₑ = ⋃ₛ Wₑ,ₛ -/
@[grind =, simp]
lemma W_mem_iff_W_s : n ∈ W e ↔ ∃ s, n ∈ W_s e s := by
  constructor
  · intro h
    simp only [W_s_ϕ_s]
    exact ϕ_complete.mp (mem_W_ϕ.mp h)
  · grind

lemma W_eq_union_W_s : W e = ⋃ (s : ℕ), W_s e s := by
  ext x
  rw [W_mem_iff_W_s]
  simp
