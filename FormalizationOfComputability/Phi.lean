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

In some sense ϕs and ϕ are merely wrappers for evaln and eval, respectively,
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
      omega
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    conv_rhs => rw [← bit_bodd_div2 n, ← bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_5]
    cases n.bodd
    <;> cases n.div2.bodd
    <;> simp [m, encodeCode, (encode_ofNatCode m), encode_ofNatCode m.unpair.1,
        encode_ofNatCode m.unpair.2, bit_val]

variable {e s t n x y r : ℕ} {X : Set ℕ}


/- ϕₑ,ₛ(n), the eth Turing program evaluated for s steps on input n.
Following Soare, we require the index, input, and output to be less than s -/
def ϕs (e s n : ℕ) : Option ℕ :=
    if (e < s) ∧ (∃ y < s, y ∈ evaln s (ofNatCode e) n)
    then evaln s (ofNatCode e) n
    else Option.none

/- ϕₑ(n), the eth Turing program evaluated on input n -/
def ϕ (e : ℕ) : ℕ →. ℕ := eval (ofNatCode e)

/- ϕₑ,ₛ(n)↓ iff it has an output -/
def ϕs_halts (e s n : ℕ) : Prop := (ϕs e s n).isSome

/- ϕₑ(n)↓ iff it has an output -/
def ϕ_halts (e n : ℕ) : Prop := (ϕ e n).Dom

/- If ϕₑ,ₛ(n)↓, then ϕₑ(n)↓ -/
lemma ϕsound (h : ϕs_halts e s n) : ϕ_halts e n := by
  have h1 : ∃ s, ϕs_halts e s n := by exact ⟨s, h⟩
  revert h1
  unfold ϕs_halts ϕs
  unfold ϕ_halts ϕ
  simp only [Part.dom_iff_mem, evaln_complete]
  grind

/- ϕₑ(n)↓ iff there is a stage s at which ϕₑ,ₛ(n)↓ -/
@[grind =, simp]
lemma ϕ_complete : ϕ_halts e n ↔ ∃ s, ϕs_halts e s n := by
  constructor
  · unfold ϕs_halts ϕ_halts ϕs ϕ
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
    exact ϕsound h

/- If ϕₑ,ₛ(n)↓, then n < s -/
@[grind →, simp]
lemma ϕ_input_bound (h : ϕs_halts e s n) : n < s := by
  simp only [ϕs_halts, ϕs, Option.mem_def, Option.isSome_iff_exists,
    Option.ite_none_right_eq_some, exists_and_left] at h
  obtain ⟨x, hx⟩ := h.right
  exact Code.evaln_bound hx

/- If ϕₑ,ₛ(n) = y, then y < s -/
@[grind →, simp]
lemma ϕ_output_bound (h : y ∈ (ϕs e s n)) : y < s := by
  simp only [ϕs, Option.mem_def, Option.ite_none_right_eq_some] at h
  grind

/- If ϕₑ,ₛ(n)↓, then e < s -/
@[grind →, simp]
lemma ϕ_index_bound (h : ϕs_halts e s n) : e < s := by grind [ϕs_halts, ϕs]

/- Helper lemmas - ϕ_{e, 0}(n)↑ -/
@[grind →, simp]
lemma halt_stage_gt_zero (h : ϕs_halts e s n) : s > 0 := by grind [ϕs_halts, ϕs]

@[grind ., simp]
lemma stage_zero_diverges : ¬ ϕs_halts e 0 n := by grind [ϕs_halts, ϕs]

/- ϕₑ,ₛ(n) is decidable -/
instance (e s n : ℕ) : Decidable (ϕs e s n).isSome :=
  (ϕs e s n).isSome.decEq true

/- ϕₑ,ₛ(n) is decidable -/
instance (e s n : ℕ) : Decidable (ϕs_halts e s n) :=
  instDecidableEqBoolIsSomeNatϕsTrue e s n

/- ϕₑ is a partial computable function -/
theorem ϕ_partrec : Nat.Partrec (ϕ e) := by
  unfold ϕ
  rw [Code.exists_code]
  use ofNatCode e

/- Monotonicity of halting: if s < t and ϕ_{e,s}(n)↓, then ϕ_{e,t}(n)↓ -/
@[grind →, simp]
lemma ϕ_halts_mono (h : s ≤ t) (h1 : ϕs_halts e s n) : ϕs_halts e t n := by
  revert h1
  simp only [ϕs_halts, ϕs, Option.mem_def, Option.isSome_iff_exists,
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
lemma ϕ_halts_mono_reverse (h : s ≤ t) (h1 : ¬ ϕs_halts e t n) : ¬ ϕs_halts e s n := by
  grind

/- The least stage s at which ϕₑ,ₛ(n)↓ (if it exists) -/
def runtime (e n : ℕ) : Part ℕ := rfind (fun s => (ϕs e s n).isSome)

/- TODO: runtime lemmas can be cleaned up with Nat.rfind spec/min? -/
/- Runtime r is minimal - if s < r, then ϕₑ,ₛ(n)↑ -/
@[simp]
lemma runtime_spec (h : r ∈ runtime e n) : ϕs_halts e r n := by
  have h1 := rfind_spec h
  simp at h1
  exact h1

lemma runtime_min (r : ℕ) (h : r ∈ (runtime e n)) : ∀ t, t < r → ¬ ϕs_halts e t n := by
  intro t ht
  have h1 := rfind_min h ht
  simp at h1
  unfold ϕs_halts
  exact Option.not_isSome_iff_eq_none.mpr h1

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
    apply runtime_spec at h
    exact ϕ_complete.mpr ⟨r, h⟩

/- The elements whose computations first halt at stage s, in ascending order.
By definition, these elements are less than s. -/
def ϕNew (e s : ℕ) : List ℕ := (List.range s).filter
  (λ n ↦ ϕs_halts e s n ∧ ¬ ϕs_halts e (s-1) n)

/- The elements in W_e enumerated up to stage s, in the order they appeared. Elements halting
at the same time are enumerated in asceding order. -/
def Ws (e : ℕ) : ℕ → List ℕ
    | 0     => []
    | s + 1 => (Ws e s) ++ ϕNew e (s+1)

/- Ws is exactly the set of n for which ϕₑ,ₛ(n)↓ -/
@[simp]
lemma Ws_mem : n ∈ Ws e s ↔ ϕs_halts e s n := by
  induction s with | zero | succ s hs
  · simp only [Ws, List.not_mem_nil, ϕs_halts, false_iff, Bool.not_eq_true,
    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    exact Option.isNone_iff_eq_none.mp rfl
  · unfold Ws
    rw [List.mem_append, hs, ϕNew]
    simp only [add_tsub_cancel_right, Bool.decide_and, List.mem_filter,
      List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    <;> intro h
    · apply Or.elim h
      <;> intro h1
      · exact ϕ_halts_mono (Nat.le_add_right s 1) h1
      · simp_all only [ϕs_halts, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none, true_and]
    · by_cases h1 : ϕs_halts e s n
      · exact Or.inl h1
      · exact Or.inr ⟨ϕ_input_bound h, ⟨h, h1⟩⟩


-- @[simp]
-- lemma Ws_gt_zero : n ∈ Ws e s → s > 0 := by
--   simp only [Ws_mem]
--   intro h
--   apply ϕ_input_bound at h
--   omega

-- @[simp]
-- lemma Ws_zero_empty : Ws e 0 = ∅ := by simp [Ws]

/- Monotonicity of W_s -/
@[simp]
lemma Ws_mono (e : ℕ) (h : s ≤ t) : (Ws e s) <+: (Ws e t) := by
  induction t generalizing s with | zero | succ t ih
  · simp_all [Ws]
  · by_cases hst : s = t+1
    · simp [hst]
    · replace h : s ≤ t := by omega
      have ht : (Ws e t) <+: (Ws e (t+1)) := by simp [Ws]
      exact List.IsPrefix.trans (ih h) ht

/- Reverse monotonicity of W_s-/
@[simp]
lemma Ws_mono_reverse (h : s ≤ t) (hx : x ∉ Ws e t) : x ∉ Ws e s := by
  contrapose hx
  exact Multiset.mem_coe.mp (List.IsPrefix.subset (Ws_mono e h) hx)

/- Membership in some W_{e,s} implies runtime r exists, and membership in W_{e, r}-/
@[grind ., simp]
lemma Ws_runtime (h : n ∈ Ws e s) : ∃ r, r ∈ runtime e n ∧ n ∈ Ws e r := by
  have ⟨r, h1⟩ := ϕ_halts_runtime_exists.mp (ϕ_complete.mpr ⟨s, Ws_mem.mp h⟩)
  refine ⟨r, ⟨h1, Ws_mem.mpr ?_⟩⟩
  exact runtime_spec h1

/- Wₑ = {n | ϕₑ(n)↓} -/
def W (e : ℕ) : Set ℕ := (ϕ e).Dom

@[simp]
lemma W_mem : n ∈ W e ↔ ϕ_halts e n := Eq.to_iff rfl

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

/- ϕₑ(x)↓ ↔ x ∈ Wₑ -/
@[simp]
lemma mem_W_ϕ : n ∈ W e ↔ ϕ_halts e n := by exact Eq.to_iff rfl

/- Wₑ,ₛ ⊆ Wₑ  -/
@[grind! ., simp]
lemma Ws_subset_W : ↑(Ws e s).toFinset ⊆ W e := by
  intro x h
  simp [Set.mem_setOf_eq] at h
  exact ϕsound h

/- Wₑ = ⋃ₛ Wₑ,ₛ -/
@[grind =, simp]
lemma W_iff_Ws : n ∈ W e ↔ ∃ s, n ∈ Ws e s := by
  constructor
  · intro h
    simp only [Ws_mem]
    exact ϕ_complete.mp (mem_W_ϕ.mp h)
  · intro ⟨s, h⟩
    simp_all only [Ws_mem, W_mem]
    exact ϕsound h

lemma W_eq_union_W_s : W e = ⋃ (s : ℕ), (Ws e s).toFinset := by
  ext x
  rw [W_iff_Ws]
  simp

open Primrec

private lemma bounded_exists_var (f : ℕ → ℕ × ℕ → Prop) [DecidableRel f] (hf : PrimrecRel f) :
    PrimrecPred (fun x : ℕ × ℕ => ∃ y < x.1, f y x) := by
  replace hf := PrimrecRel.exists_mem_list hf
  unfold PrimrecRel at hf
  have hpair : Primrec (fun x : ℕ × ℕ => (List.range x.1, x)) := by
    exact (Primrec.list_range.comp Primrec.fst).pair Primrec.id
  replace hf := hf.comp hpair
  simpa only [List.mem_range] using hf

/- ϕₑ,ₛ is a primitive recursive function -/
lemma ϕs_primrec₂ : Primrec₂ (ϕs e) := by
  unfold Primrec₂
  have h := primrec_evaln.comp (pair (pair fst (const (ofNatCode e))) snd)
  apply ite (PrimrecPred.and (PrimrecRel.comp nat_lt (const e) fst) ?_) h (const Option.none)
  apply bounded_exists_var
  simp only [PrimrecRel, Option.mem_def]
  exact PrimrecRel.comp Primrec.eq (.comp h snd) (option_some_iff.mpr fst)

/- ϕₑ,ₛ(n)↓ is a primitive recursive relative -/
lemma ϕs_halts_primrecRel (e : ℕ) : PrimrecRel (fun s n : ℕ => ϕs_halts e s n) := by
  unfold ϕs_halts
  apply Primrec.primrecPred
  simp [Option.isSome_iff_exists]
  exact Primrec.option_isSome.comp ((ϕs_primrec₂ (e := e)).comp fst snd)

/- ϕNew is a primitive recursive function -/
lemma ϕNew_primrec (e : ℕ) : Primrec (ϕNew e) := by
  let R : ℕ → ℕ → Prop := fun n s => ϕs_halts e s n ∧ ¬ ϕs_halts e (s - 1) n
  have hpred : Primrec₂ fun (n : ℕ) (s : ℕ) => s - 1 := Primrec₂.comp nat_sub snd (Primrec.const 1)
  have hR1 := PrimrecRel.comp₂ (ϕs_halts_primrecRel e) hpred
    (Primrec₂.left : Primrec₂ fun (n : ℕ) (_s : ℕ) => n)
  have hR : PrimrecRel R := by
    dsimp [R]
    change PrimrecPred fun p : ℕ × ℕ => ϕs_halts e p.2 p.1 ∧ ¬ ϕs_halts e (p.2 - 1) p.1
    exact PrimrecPred.and (ϕs_halts_primrecRel e).swap (PrimrecPred.not hR1)
  exact ((PrimrecRel.listFilter hR).comp Primrec.list_range Primrec.id).of_eq fun s => by
    simp [ϕNew, R]

lemma Ws_primrec (e : ℕ) (hϕNew : Primrec (ϕNew e)) : Primrec (Ws e) := by
  have hϕNew₂ : Primrec₂ fun (s : ℕ) (L : List ℕ) => ϕNew e (s + 1) := by
    refine Primrec.comp₂ hϕNew (comp₂ succ Primrec₂.left)
  have hstep := Primrec₂.comp₂ Primrec.list_append
    (Primrec₂.right : Primrec₂ fun (_s : ℕ) (L : List ℕ) => L) hϕNew₂
  exact (Primrec.nat_rec₁ ([] : List ℕ) hstep).of_eq fun s => by induction s with
    | zero => simp [Ws]
    | succ s ih => simp [Ws, ih]
