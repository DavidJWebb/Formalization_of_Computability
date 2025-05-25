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

theorem set_pi01_union (X Y : Set ℕ) (hX : Pi01 X) (hY : Pi01 Y) : Pi01 (X∪Y) := by
  unfold Pi01
  rw [Set.compl_union]
  apply set_sigma01_inter
  exact hX
  exact hY

theorem set_pi01_inter (X Y : Set ℕ) (hX : Pi01 X) (hY : Pi01 Y) : Pi01 (X∩Y) := by
  unfold Pi01
  rw [Set.compl_inter]
  apply set_sigma01_union
  exact hX
  exact hY

-- sigma01_compl_iff_pi01
-- pi01_compl_iff sigma01
-- finite_set_pi01
-- set_pi01_sdiff_computable

theorem finite_set_pi01 (X : Set ℕ) (h: Finite X) : Pi01 X:= by
apply cofinite_set_sigma01
rw [compl_compl]
exact h

-- cofinite_set_pi01
-- set_pi01_symdiff_finite

def nat_function_partrec (f : ℕ →. Unit) : ℕ →. ℕ :=
f.map (fun _ => 1)

lemma sigma01_has_delta01_subset (X : Set ℕ) (hX : Sigma01 X) (hInf : Infinite X):
∃ (Y : Set ℕ), Delta01 Y ∧ Infinite Y ∧ Y ⊆ X := by
obtain ⟨f, ⟨hfPart, hfDom⟩⟩ := hX
let g := f.map (fun _ => 1)
have hfg : ∀ (x:ℕ), (f x) = some () ↔ (g x) = 1 := by
  sorry
have hgPart : Nat.Partrec g := by
  sorry
rw [Nat.Partrec.Code.exists_code] at hgPart
obtain ⟨e, he⟩ := hgPart
sorry

-- Views Of Mount Σ01 :
-- partial recursive f
-- its domain X
-- the range of a computable g : ℕ → ℕ
-- the code e for f
-- the (possibly finite) sequence of nth outputs {fn}
-- the infinite partial recursive sequence of nth outputs {fn}


-- lemma : an increasing partial recursive sequence


-- eval x c = 1 ↔ ∃ s=(μ t) evaln x c t = 1 (essentially, s = the stage ϕₑ(x) halts)
-- s(n) = min(n, the halt time of n) is a partial function


let g (f : ℕ → Bool) (n : ℕ) : ℕ :=
  if h₁ : n > 0 ∧ f (n - 1) = () then
    Nat.rfind (λ a => a > (n - 1) ∧ (f a)=())
  else
    false
-- Say X = Wₑ, i.e. e is the index of a partial recursive function f with domain X
-- Let g 0 = μ y {y ∈ f.Dom}
-- Let g n = μ y {y > g(n-1) ∧ y ∈ X}
-- Then Y = g.Dom ⊆ X
-- Show that as X is infinite, so is Y

def Coinfinite (X : Set ℕ) : Prop := Xᶜ.Infinite

def Inf_coinf (X : Set ℕ) : Prop := Infinite X ∧ Coinfinite X

def Immune (X : Set ℕ) : Prop := ∀ (Y : Set ℕ), (Delta01 Y ∧ Infinite Y) → ¬ (Y ⊆ X)
--equivalently, this can be defined with Sigma01 sets - see below

lemma immune_is_inf_coinf (X : Set ℕ) (hX : Immune X) : Infinite X → Coinfinite X := by
  intro h
  rw [Set.infinite_coe_iff] at h
  by_contra h1
  revert hX
  simp
  unfold Immune
  push_neg
  use X
  constructor
  · simp [Coinfinite] at h1
    rw [← Set.finite_coe_iff] at h1
    apply finite_set_delta01 at h1
    rw [set_delta01_compl_iff, compl_compl] at h1
    constructor
    · exact h1
    · exact Set.infinite_coe_iff.mpr h
  · rfl

lemma sigma01_not_immune (X : Set ℕ) (hX : Sigma01 X) : ¬(Finite X) → ¬ Immune X := by
intro hInf
unfold Immune
push_neg
sorry -- use the Delta01 subset of Y guaranteed by lemma

def Sigma01_Immune (X : Set ℕ) : Prop := ∀ (Y : Set ℕ), (Sigma01 Y ∧ Infinite Y) → ¬ (Y ⊆ X)

lemma immune_iff_sigma01_immune (X : Set ℕ) : Immune X ↔ Sigma01_Immune X := by
constructor
· sorry
· sorry

def Cohesive (C : Set ℕ) : Prop := ∀ (X : Set ℕ), (Sigma01 X) → ((X∩C).Finite  ∨ (Xᶜ∩C).Finite)
-- C is infinite, and for all Σ⁰₁ sets X, if X ⊆ C, then (X∩C is finite) or (Xᶜ∩C is finite)

--this proof may be replaced when I add finer grained notions like hyperimmune
lemma coh_is_immune (C : Set ℕ) (hC : Cohesive C) : Immune C := by
  rw [immune_iff_sigma01_immune]
  by_contra h
  revert hC
  simp
  unfold Cohesive
  push_neg
  unfold Sigma01_Immune at h
  push_neg at h
  obtain ⟨Y, ⟨⟨hYSigma, hYInf⟩, hYC⟩⟩ := h
  use Y
  constructor
  · exact hYSigma
  · constructor
    · have hYinter : Y ∩ C = Y := by simp [hYC]
      rw [hYinter]
      rw [← not_finite_iff_infinite, Set.finite_coe_iff] at hYInf
      exact hYInf
    · sorry

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

lemma Coh_not_split_Pi01 (C : Set ℕ) (hC : Cohesive C) :
∀ (X : Set ℕ), (Pi01 X) → ((X∩C).Finite  ∨ (Xᶜ∩C).Finite) := by
intro X hX
nth_rw 1 [← compl_compl X]
rw [Or.comm]
apply hC
exact hX

def Pi01Immune (X : Set ℕ) : Prop :=
∀ (Y : Set ℕ), (Pi01 Y) → (Infinite Y) → ¬Y⊆X

theorem pi01Immune_is_immune (X : Set ℕ) (hX: Pi01Immune X) : Immune X := by
by_contra h
revert hX
unfold Immune at h
unfold Pi01Immune
push_neg at h
simp
obtain ⟨Y, ⟨⟨hYSigma, hYInf⟩, hYX⟩⟩ := h
use Y
constructor
· apply delta01_is_pi01
  exact hYSigma
· constructor
  · exact hYInf
  · exact hYX

-- cohesive sets are either Pi01 iff they are not Pi01-immune
theorem Pi01Cohesive (C : Set ℕ) (hC: Cohesive C): Inf_coinf C → (Pi01 C ↔ ¬ Pi01Immune C) := by
intros hInf
unfold Pi01Immune
push_neg
constructor
· intro hP
  use C -- this direction is trivial, as C ⊆ C ∈ Π⁰₁
  constructor
  · exact hP
  · constructor
    · exact hInf.left
    · simp
· intro h3 -- first say let Y be an infinite Π⁰₁ subset of C
  obtain ⟨Y, ⟨hYPi, ⟨hYInf, hXC⟩⟩⟩ := h3
  have hY1: Y ∩ C = Y := by simp [hXC]
  have h2: ((Y∩C).Finite  ∨ (Yᶜ∩C).Finite) := by -- as C is cohesive, it cannot be split by a Π⁰₁ set
    apply Coh_not_split_Pi01 C hC
    exact hYPi
  rw [hY1] at h2
  rcases h2 with h2 | h2
  · rw [← Set.finite_coe_iff] at h2
    by_contra -- this case is a contradiciton, Y cannot both be infinite and finite
    revert h2
    simp
    exact hYInf
  · rw [← Set.inter_union_compl C Y, Set.inter_comm, hY1]
    apply set_pi01_union -- C is exactly Y with finitely many more elements
    · exact hYPi
    · apply finite_set_pi01
      rw [Set.inter_comm]
      exact h2
