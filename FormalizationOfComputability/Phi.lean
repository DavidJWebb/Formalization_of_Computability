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
the use functions ϕₑ and the enumerable sets Wₑ. The former is present in Partrec.code as eval,
so much of this file can be thought of as a wrapper for that one.
-/

namespace Nat.Partrec.Code

/- noncomputable def μ (P : ℕ → Prop) [DecidablePred P] (h : ∃ n, P n) : ℕ :=
Nat.find h -/

/- ϕₑ,ₛ(_) -/
def Phi_stage (e s : ℕ) : ℕ → Option ℕ :=
    Code.evaln s (Code.ofNatCode e)
/- ϕₑ(_) -/
def Phi (e : ℕ) : ℕ →. ℕ :=
    (Code.ofNatCode e).eval
/- halting -/
def Phi_stage_halts (e s n : ℕ) : Prop :=
    ∃ (x : ℕ), x ∈ Phi_stage e s n
def Phi_halts (e n : ℕ) : Prop :=
    ∃ (x : ℕ), x ∈ Phi e n
def Phi_stage_diverges (e s n : ℕ) : Prop :=
    ¬ Phi_stage_halts e s n
def Phi_diverges (e n : ℕ) : Prop :=
    ¬ Phi_halts e n
/- Wₑ,ₛ = {n | n ≤ s ∧ ϕₑ,ₛ(n)↓} -/
def W_stage (e s : ℕ) : Finset ℕ :=
    (Finset.range (s)).filter (λ n => (Phi_stage e s n).isSome)
/- Wₑ = {n | n ≤ s ∧ ϕₑ(n)↓} -/
def W (e : ℕ) : Set ℕ := (Phi e).Dom

lemma phi_stage_primrec (e s : ℕ) : Primrec (Phi_stage e s) := by
  have h : Primrec (fun ((s, e), n) => Code.evaln s e n) := by
    exact primrec_evaln
  unfold Phi_stage
  refine Primrec.encode_iff.mp ?_
  refine Primrec'.prim_iff₁.mp ?_

lemma phi_partrec (e : ℕ) : Partrec (Phi e) := by
  unfold Phi
  rw [exists_code]
  use ofNatCode e

lemma W_stage_primrec (e s : ℕ) : set_primrec (W_stage e s) := by
  sorry

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

/- ϕₑ(n)↓ ↔ ∃ (s : ℕ), ϕₑ,ₛ(n)↓ -/
theorem phi_halts_runtime_exists (e n : ℕ) : Phi_halts e n ↔ ∃ (s : ℕ), Phi_stage_halts e s n := by
  unfold Phi_stage_halts Phi_halts Phi_stage Phi
  simp [evaln_complete]
  exact exists_comm

/- s < t → ϕₑ,ₛ(n)↓ → ϕₑ,ₜ(n)↓ -/
theorem phi_halts_mono (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_stage_halts e s n) :
    Phi_stage_halts e t n := by
  revert h1
  unfold Phi_stage_halts Phi_stage
  intro h1
  obtain ⟨x, hx⟩ := h1
  use x
  apply Nat.Partrec.Code.evaln_mono h hx

/- the least time that it takes for ϕ to halt (if it does)-/
def runtime (e n : ℕ) : Part ℕ :=
  rfindOpt (fun s => if (Phi_stage e s n).isSome then some s else Option.none)

theorem runtime_is_min (e n s t : ℕ) (h1 : s ∈ (runtime e n)) :
    Phi_stage_halts e s n ∧ (t < s → Phi_stage_diverges e t n) := by
  simp [runtime, rfindOpt] at h1
  obtain ⟨⟨hs, hs2⟩, hs⟩ := h1
  unfold Phi_stage_halts
  constructor
  · rw [Option.isSome_iff_exists] at hs
    obtain ⟨a, h⟩ := hs
    use a
    exact h
  · intro h
    apply hs2 at h
    unfold Phi_stage_diverges Phi_stage_halts
    rw [h]
    simp

theorem halt_implies_runtime_gt_input (e s x n : ℕ) (h : x ∈ (Phi_stage e s n)): n < s := by
  unfold Phi_stage at h
  apply Code.evaln_bound
  exact h

/- ϕₑ,ₛ(x)↓ ↔ x ∈ Wₑ,ₛ -/
lemma W_stage_phi_stage (e s n : ℕ) : n ∈ W_stage e s ↔ Phi_stage_halts e s n := by
unfold W_stage Phi_stage_halts
simp
constructor
· intro ⟨h1, h2⟩
  rw [Option.isSome_iff_exists] at h2
  exact h2
· intro h
  obtain ⟨x, h⟩ := h
  rw [Option.isSome_iff_exists]
  constructor
  · unfold Phi_stage at h
    apply Code.evaln_bound at h
    exact h
  · use x

/- ϕₑ(x)↓ ↔ x ∈ Wₑ -/
lemma mem_W_phi (e n : ℕ) : n ∈ W e ↔ Phi_halts e n := by
unfold W Phi_halts
exact Part.dom_iff_mem

/- Wₑ,ₛ ⊆ Wₑ  -/
theorem W_stage_subset_W (e s : ℕ) : (W_stage e s).toSet ⊆ W e := by
  intro x h
  simp [W_stage] at h
  simp [W]
  obtain ⟨h1, h2⟩ := h
  rw [Option.isSome_iff_exists] at h2
  obtain ⟨a, hx⟩ := h2
  rw [← Phi_halts]
  rw [phi_halts_runtime_exists]
  apply Exists.intro s
  apply Exists.intro a
  exact hx

theorem W_mem_iff_W_stage (e n: ℕ) : n ∈ W e ↔ ∃ (s : ℕ), n ∈ W_stage e s :=by
constructor
· intro h
  apply Part.dom_iff_mem.mp at h
  rw [← Phi_halts] at h
  rw [phi_halts_runtime_exists] at h
  obtain ⟨s, h⟩ := h
  use s
  rw [W_stage_phi_stage]
  exact h
· intro h
  obtain ⟨s, h⟩ := h
  apply W_stage_subset_W
  exact h

/- Wₑ = ⋃ₛ Wₑ,ₛ -/
theorem W_eq_union_W_stage (e : ℕ) : W e = ⋃ (s : ℕ), W_stage e s := by
ext x
rw [W_mem_iff_W_stage]
simp

/- The elements that have entered W_e at stage s-/
def W_stage_new (e s : ℕ) : List ℕ :=
  List.range (s + 1) |>
    List.filter (λ n => (Phi_stage e s n).isSome ∧
                         (s = 0 ∨ (Phi_stage e (s - 1) n).isNone))

/- lemma W_stage_new_eq (e s : ℕ) (h : s > 0): Set ℕ :=
  W_stage_new = (W_stage e s) \ (W_stage e (s-1)) -/
  -- note "=" is innacurate, the left side must be coerced to Set ℕ

def W_enum (e : ℕ) : ℕ → List ℕ
| 0     => W_stage_new e 0
| s + 1 =>
  let prev := W_enum e s
  let delta := W_stage_new e (s + 1)
  prev ++ delta.filter (λ n => n ∉ prev)

lemma inf_inc_sigma01_seq_is_delta01 (e : ℕ) (h1 : (W e).Infinite)
    (h2 : ∀ (n : ℕ), W_enum n < W_enum (n+1)) :
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
