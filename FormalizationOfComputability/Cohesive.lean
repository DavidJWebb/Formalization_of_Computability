/- Still missing the main lemma that every infinite Sigma01 set has
an infinite Delta01 subset. That will appear in Phi.lean -/

/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.Sets
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Linarith

namespace Computability

abbrev Delta01 := Computable.set
abbrev Sigma01 := Partrec.set

def Coinfinite (X : Set ℕ) : Prop := Xᶜ.Infinite
def Inf_coinf (X : Set ℕ) : Prop := X.Infinite ∧ Coinfinite X

def Evens : Set ℕ := {n | n % 2 = 0}
def Odds : Set ℕ := {n | n % 2 = 1}

lemma evens_eq_odds_compl : Evens = Oddsᶜ := by
  ext x
  simp [Evens, Odds]

lemma odds_eq_evens_compl : Odds = Evensᶜ := by
  simp [evens_eq_odds_compl]

lemma evens_infinite : Evens.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  use 2*a+2
  constructor
  · unfold Evens
    refine Set.mem_setOf.mpr ?_
    simp
  · linarith

lemma odds_infinite : Odds.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  use 2*a+1
  constructor
  · unfold Odds
    refine Set.mem_setOf.mpr ?_
    simp
  · linarith

open Primrec

lemma Primrec.set_evens : Primrec.set Evens := by
  let f: ℕ → Bool := fun x => decide (x % 2 = 0)
  use f
  constructor
  · apply Primrec.ite (PrimrecRel.comp Primrec.eq ?_ (.const 0)) (.const true) (.const false)
    exact Primrec₂.comp .nat_mod .id (const 2)
  · intro x
    simp [f, Evens]

lemma set_delta01_evens : Computable.set Evens := Computable.primrec Primrec.set_evens

lemma set_sigma01_evens : Sigma01 Evens := Partrec.computable set_delta01_evens

def Pi01 (X : Set ℕ): Prop := Sigma01 Xᶜ

theorem delta01_is_sigma01 (X : Set ℕ) (h: Delta01 X) : Sigma01 X := Partrec.computable h

theorem delta01_is_pi01 (X : Set ℕ) (h: Delta01 X) : Pi01 X :=
  Partrec.computable (Computable.compl h)

theorem delta01_iff_sigma01_and_pi01 (X : Set ℕ) : Delta01 X ↔ Sigma01 X ∧ Pi01 X := by
  constructor
  · intro h
    constructor
    · apply delta01_is_sigma01
      exact h
    · apply delta01_is_pi01
      exact h
  · intro h
    obtain ⟨⟨f, ⟨fSigma, fSpec⟩⟩, ⟨g, ⟨gPi, gSpec⟩⟩⟩ := h
    sorry

-- nat_pi01
-- empty_set_pi01
-- singleton_pi01

theorem set_pi01_union (X Y : Set ℕ) (hX : Pi01 X) (hY : Pi01 Y) : Pi01 (X∪Y) := by
  unfold Pi01
  rw [Set.compl_union]
  exact Partrec.inter hX hY

theorem set_pi01_inter (X Y : Set ℕ) (hX : Pi01 X) (hY : Pi01 Y) : Pi01 (X∩Y) := by
  unfold Pi01
  rw [Set.compl_inter]
  exact Partrec.union hX hY

-- sigma01_compl_iff_pi01
-- pi01_compl_iff sigma01
-- finite_set_pi01
-- set_pi01_sdiff_computable

theorem finite_set_pi01 (X : Set ℕ) (h: Finite X) : Pi01 X:= by
apply Partrec.cofinite
rw [compl_compl]
exact h

-- cofinite_set_pi01
-- set_pi01_eq_star_iff

def nat_function_partrec (f : ℕ →. Unit) : ℕ →. ℕ :=
f.map (fun _ => 1)

lemma sigma01_has_delta01_subset (X : Set ℕ) (hX : Sigma01 X) (hInf : X.Infinite):
∃ (Y : Set ℕ), Delta01 Y ∧ Y.Infinite ∧ Y ⊆ X ∧ (X\Y).Infinite := by
obtain ⟨f, ⟨hfPart, hfDom⟩⟩ := hX
let g := f.map (fun _ => 1)
have hfg : ∀ (x:ℕ), (f x) = some () ↔ (g x) = 1 := by
  sorry
have hgPart : Nat.Partrec g := by
  sorry
rw [Nat.Partrec.Code.exists_code] at hgPart
obtain ⟨e, he⟩ := hgPart
sorry

def Immune (X : Set ℕ) : Prop := ∀ (Y : Set ℕ), (Delta01 Y ∧ Y.Infinite) → ¬ (Y ⊆ X)
--equivalently, this can be defined with Sigma01 sets - see below

def Simple (X : Set ℕ) : Prop := Pi01 X ∧ Immune X

lemma immune_is_coinf (X : Set ℕ) (hX : Immune X) : Coinfinite X := by
  by_cases hInf : X.Finite
  · exact Set.Finite.infinite_compl hInf
  · by_contra h1
    revert hX
    simp
    unfold Immune
    push_neg
    use X
    constructor
    · simp [Coinfinite] at h1
      rw [← Set.finite_coe_iff] at h1
      apply Computable.finite at h1
      rw [Computable.compl_iff, compl_compl] at h1
      constructor
      · exact h1
      · exact hInf
    · rfl

lemma sigma01_not_immune (X : Set ℕ) (hX : Sigma01 X) (hInf : X.Infinite) : ¬ Immune X := by
unfold Immune
push_neg
apply sigma01_has_delta01_subset at hX
apply hX at hInf
obtain ⟨Y, ⟨hYDelta, ⟨hYInf, hYX⟩⟩⟩ := hInf
use Y
constructor
· constructor
  · exact hYDelta
  · exact hYInf
· exact hYX.left

def Sigma01_Immune (X : Set ℕ) : Prop := ∀ (Y : Set ℕ), (Sigma01 Y ∧ Y.Infinite) → ¬ (Y ⊆ X)

lemma immune_iff_sigma01_immune (X : Set ℕ) : Immune X ↔ Sigma01_Immune X := by
constructor
· intro h Y ⟨h₁, h₂⟩
  apply sigma01_has_delta01_subset at h₁
  apply h₁ at h₂
  obtain ⟨Z, ⟨hZDelta, ⟨hZInf, hZY⟩⟩⟩ := h₂
  by_contra h₃
  revert h
  unfold Immune
  simp
  use Z
  constructor
  · exact hZDelta
  · constructor
    · exact hZInf
    · exact subset_trans hZY.left h₃
· intro h Y ⟨h₁, h₂⟩
  apply delta01_is_sigma01 at h₁
  apply h
  constructor
  · exact h₁
  · exact h₂

def CEMaximal (M : Set ℕ) : Prop := Sigma01 M ∧
    ∀ (X : Set ℕ), Sigma01 X → M ⊆ X → (Xᶜ.Finite ∨ (X \ M).Finite)
def Cohesive (C : Set ℕ) : Prop := ∀ (X : Set ℕ), (Sigma01 X) → ((X∩C).Finite  ∨ (Xᶜ∩C).Finite)

lemma cohesive_is_coinf (C : Set ℕ) (hC : Cohesive C) : Coinfinite C := by
  contrapose hC
  unfold Coinfinite at hC
  rw [Set.not_infinite] at hC
  unfold Cohesive
  push_neg
  use Evens
  constructor
  · exact set_sigma01_evens
  · constructor
    · have h : eq_star Evens (Evens ∩ C) := by
        unfold eq_star
        simp [Set.symmDiff_def]
        constructor
        · exact Set.Finite.subset hC (Set.diff_subset_compl Evens C)
        · rw [Set.inter_diff_assoc Evens]
          simp
      exact infinite_eq_star h evens_infinite
    · rw [odds_eq_evens_compl.symm]
      have h : eq_star Odds (Odds ∩ C) := by
        unfold eq_star
        simp [Set.symmDiff_def]
        constructor
        · exact Set.Finite.subset hC (Set.diff_subset_compl Odds C)
        · rw [Set.inter_diff_assoc Odds]
          simp
      exact infinite_eq_star h odds_infinite

lemma cohesive_is_not_sigma01 (C : Set ℕ) (hC : Cohesive C) (hCInf : C.Infinite) : ¬ Sigma01 C := by
  by_contra h1
  apply sigma01_has_delta01_subset at h1
  obtain ⟨Y, ⟨hY, ⟨hYInf, ⟨hYC, hY2⟩⟩⟩⟩:= h1 hCInf
  apply delta01_is_sigma01 at hY
  apply hC at hY
  revert hY
  rw [← Set.inter_eq_left] at hYC
  rw [hYC]
  simp
  constructor
  · rw [← Set.not_finite]
    exact hYInf
  · rw [← Set.diff_eq_compl_inter]
    exact hY2

theorem cemaximal_iff_compl_cohesive (M : Set ℕ) (hM: Sigma01 M) :
    CEMaximal M ↔ Cohesive Mᶜ := by
  constructor
  · intro h W hW
    have hXuM : Sigma01 (M∪W) := by
      exact Partrec.union hM hW
    have h1 : W ∩ Mᶜ = (W ∪ M)\ M := by
      rw [Set.union_diff_right]
      exact rfl
    have h2 : M ⊆ M∪W:= by simp
    rw [h1]
    rw [Set.inter_eq_compl_compl_union_compl, compl_compl, compl_compl]
    apply h.right at hXuM
    apply hXuM at h2
    symm
    rw [Set.union_comm M W] at h2
    exact h2
  · intro h
    constructor
    · exact hM
    · intro W hW hMW
      apply h at hW
      have h1 : Wᶜ = Wᶜ ∩ Mᶜ := by simp [hMW]
      rw [h1]
      symm
      exact hW

lemma coh_is_immune (C : Set ℕ) (hC : Cohesive C) : Immune C := by
  by_cases hInf : C.Finite
  · unfold Immune
    intro A ⟨hA, hAInf⟩
    by_contra h
    revert hAInf
    simp
    exact Set.Finite.subset hInf h
  · rw [immune_iff_sigma01_immune]
    unfold Sigma01_Immune
    intro Y ⟨hY, hYInf⟩
    have hY2 := hY
    apply hC at hY
    rcases hY with hY | hY
    · by_contra h
      revert hY
      rw [← Set.inter_eq_left] at h
      rw [h]
      exact hYInf
    · by_contra h
      rw [← Set.diff_eq_compl_inter] at hY
      have h1 : eq_star Y C := by
        unfold eq_star
        rw [Set.symmDiff_def]
        simp
        constructor
        · rw [Set.diff_eq_empty.mpr h]
          simp
        · exact hY
      apply Partrec.eq_star at hY2
      apply cohesive_is_not_sigma01 at hC
      revert hC
      simp
      constructor
      · exact hInf
      · exact hY2
      exact h1

lemma Coh_not_split_Pi01 (C : Set ℕ) (hC : Cohesive C) :
∀ (X : Set ℕ), (Pi01 X) → ((X∩C).Finite  ∨ (Xᶜ∩C).Finite) := by
intro X hX
nth_rw 1 [← compl_compl X]
rw [Or.comm]
exact hC Xᶜ hX

def Pi01Immune (X : Set ℕ) : Prop :=
∀ (Y : Set ℕ), (Pi01 Y) → (Y.Infinite) → ¬Y⊆X

theorem pi01Immune_is_immune (X : Set ℕ) (hX: Pi01Immune X) : Immune X := by
  by_contra h
  revert hX
  unfold Immune at h
  unfold Pi01Immune
  push_neg at h
  simp
  obtain ⟨Y, ⟨⟨hYDelta01, hYInf⟩, hYX⟩⟩ := h
  use Y
  constructor
  · exact delta01_is_pi01 Y hYDelta01
  · constructor
    · exact hYInf
    · exact hYX

-- cohesive sets are Pi01 iff they are not Pi01-immune
theorem Pi01Cohesive (C : Set ℕ) (hC: Cohesive C): Inf_coinf C → (Pi01 C ↔ ¬ Pi01Immune C) := by
  intro ⟨hInf, hCInf⟩
  unfold Pi01Immune
  push_neg
  constructor
  · intro hP
    use C -- this direction is trivial, as C ⊆ C ∈ Π⁰₁
  · intro h3 -- first say let Y be an infinite Π⁰₁ subset of C
    obtain ⟨Y, ⟨hYPi, ⟨hYInf, hXC⟩⟩⟩ := h3
    have hY1: Y ∩ C = Y := by simp [hXC]
    have h2: ((Y∩C).Finite  ∨ (Yᶜ∩C).Finite) := Coh_not_split_Pi01 C hC Y hYPi
    -- as C is cohesive, it cannot be split by a Π⁰₁ set
    rw [hY1] at h2
    rcases h2 with h2 | h2
    · rw [← Set.finite_coe_iff] at h2
      by_contra -- this case is a contradiciton, Y cannot both be infinite and finite
      revert h2
      simp only [imp_false, not_finite_iff_infinite]
      exact Set.infinite_coe_iff.mpr hYInf
    · rw [← Set.inter_union_compl C Y, Set.inter_comm, hY1]
      apply set_pi01_union -- C is exactly Y with finitely many more elements
      · exact hYPi
      · apply finite_set_pi01
        rw [Set.inter_comm]
        exact h2
