-- most of this is a work in progress, the main tools are in SetPrimRec

/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/

import FormalizationOfComputability.SetPrimRec

set_option warningAsError false

def Pi01 (X : Set ℕ): Prop := Sigma01 Xᶜ

def Inf_coinf (X : Set ℕ) :Prop := X.Infinite ∧ Xᶜ.Infinite

lemma Pi01_fin_diff (X D : Set ℕ) (hX : Pi01 X) (hD : Finite D) : Pi01 (X∪D) := by
sorry

def Cohesive (C : Set ℕ) : Prop := Inf_coinf C →
∀ (X : Set ℕ ), (Sigma01 X) → ((X∩C).Finite  ∨ (Xᶜ∩C).Finite)
-- C is infinite, and for all Σ⁰₁ sets X, if X ⊆ C, then (X∩C is finite) or (Xᶜ∩C is finite)

lemma Coh_not_split_Pi01 (C X : Set ℕ) (hC: Cohesive C): Inf_coinf C → Pi01 X → ((X∩C).Finite  ∨ (Xᶜ∩C).Finite) := by
intros hInf hX
unfold Pi01 at hX
nth_rw 1 [← compl_compl X]
rw [Or.comm]
apply hC hInf
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
