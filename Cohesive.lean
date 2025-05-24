  -- most of this is a work in progress, the main tools are in SetPrimRec

/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/

import FormalizationOfComputability.SetPrimRec

set_option warningAsError false

def Pi01 (X : Set ℕ): Prop := Sigma01 Xᶜ

theorem delta01_is_sigma01 (X : Set ℕ) (h: Delta01 X) : Sigma01 X := by
apply set_computable_is_sigma01
exact h

theorem delta01_is_pi01 (X : Set ℕ) (h: Delta01 X) : Pi01 X := by
apply set_computable_is_sigma01
apply set_computable_compl
exact h

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
-- set_pi01_union
-- set_pi01_inter
-- sigma01_compl_is_pi01
-- pi01_compl_is_sigma01
-- finite_set_pi01
-- set_pi01_sdiff_computable
-- finite_set_pi01
-- cofinite_set_pi01
-- set_pi01_symdiff_finite

def Inf_coinf (X : Set ℕ) :Prop := X.Infinite ∧ Xᶜ.Infinite

lemma Pi01_fin_diff (X D : Set ℕ) (hX : Pi01 X) (hD : Finite D) : Pi01 (X∪D) := by
sorry

def Immune (X : Set ℕ) : Prop := ∀ (Y : Set ℕ), Sigma01 Y → Infinite Y → ¬ (Y ⊆ X)

def Cohesive (C : Set ℕ) : Prop := Inf_coinf C ∧
∀ (X : Set ℕ ), (Sigma01 X) → ((X∩C).Finite  ∨ (Xᶜ∩C).Finite)
-- C is infinite, and for all Σ⁰₁ sets X, if X ⊆ C, then (X∩C is finite) or (Xᶜ∩C is finite)

--this proof will be replaced when I add finer grained notions like hyperimmune
lemma coh_is_immune (C : Set ℕ) (hC : Cohesive C) : Immune C := by
  by_contra h
  revert hC
  simp
  unfold Cohesive
  push_neg
  intro hCInf
  unfold Immune at h
  push_neg at h
  obtain ⟨Y, ⟨hYSigma, ⟨hYInf, hYC⟩⟩⟩ := h
  use Y
  constructor
  · exact hYSigma
  · constructor
    · have hYinter : Y ∩ C = Y := by simp [hYC]
      rw [hYinter]
      rw [← not_finite_iff_infinite, Set.finite_coe_iff] at hYInf
      exact hYInf
    ·
/-
  apply hC.right at hYSigma
  rw [← not_finite_iff_infinite, Set.finite_coe_iff] at hYInf
  rw [hYinter, or_comm, or_iff_not_imp_right] at hYSigma
  simp [hYInf, ← Set.diff_eq_compl_inter] at hYSigma -/

  -- Y =* C, Y ∩ C = Y = Infinite, Yᶜ ∩ C =* Cᶜ = Infinite

def Evens : Set ℕ := {n | n % 2 = 0}

lemma set_primrec_evens : set_primrec Evens := by
  let f: ℕ → Bool := fun x => decide (x % 2 = 0)
  use f
  constructor
  · apply Primrec.ite
    · refine PrimrecRel.comp ?_ ?_ ?_
      · exact Primrec.eq
      · refine Primrec₂.comp ?_ ?_ ?_
        · exact Primrec.nat_mod
        · exact Primrec.id
        · exact Primrec.const 2
      · exact Primrec.const 0
    · exact Primrec.const true
    · exact Primrec.const false
  · intro x
    simp [f]
    unfold Evens
    simp

lemma set_delta01_evens : set_computable Evens := by
  apply set_primrec_is_computable
  exact set_primrec_evens

lemma set_sigma01_evens : Sigma01 Evens := by
  apply set_delta01_is_sigma01
  exact set_delta01_evens


lemma Coh_not_split_Pi01 (C X : Set ℕ) (hC : Cohesive C) (hX : Pi01 X) :
((X∩C).Finite  ∨ (Xᶜ∩C).Finite) := by
unfold Pi01 at hX
nth_rw 1 [← compl_compl X]
rw [Or.comm]
apply hC.right
exact hX

def Pi01Immune (A : Set ℕ) : Prop := Inf_coinf A →
∀ (X : Set ℕ), (Pi01 X) → (X.Infinite) → ¬X⊆A

--TODO: clean up using set_partrec lemmas
theorem Pi01Cohesive (C : Set ℕ) (hC: Cohesive C): Inf_coinf C → (Pi01 C ↔ ¬ Pi01Immune C) := by
intros hInf
constructor
· intro hP -- this direction is trivial, as C ⊆ C ∈ Π⁰₁
  unfold Pi01Immune
  push_neg
  constructor
  · exact hInf
  · use C
    constructor
    · exact hP
    · constructor
      · exact hInf.left
      · simp
· unfold Pi01Immune -- first say that Y is a Π⁰₁ subset of C
  push_neg
  intro h3
  obtain ⟨Y, hY⟩ := h3.right
  have hY1: Y ∩ C = Y := by
    simp
    exact hY.right.right
  have h5: ((Y∩C).Finite  ∨ (Yᶜ∩C).Finite) := by -- as C is cohesive, it cannot be split by a Π⁰₁ set
    apply Coh_not_split_Pi01 C Y hC hInf
    exact hY.left
  rw [hY1] at h5
  rcases h5 with h51 | h52
  · have hY2 := hY.right.left -- Y∩C = Y is infinite, ruling one case out
    tauto
  · have hCY : C = (Y ∩ C) ∪ (Yᶜ ∩ C) := by
      repeat rw [Set.inter_comm _ C]
      rw [Set.inter_union_compl]
    rw [hCY, hY1]
    apply Pi01_fin_diff
    exact hY.left
    exact h52
