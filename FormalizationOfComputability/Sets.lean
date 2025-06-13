/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import Mathlib.Computability.Halting
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Sets for Computability Theory
This file provides definitions of subsets of ℕ to be primitive/partial recursive and computable.
This allows for set operations such as union, intersection, set difference, and complement.

## Main results
- Implications among primitive recursive, computable, and partially recursive sets
- ℕ, the empty set, singletons, finite, and cofinite sets are primitive recursive
- All three notions are closed under union and intersection
- Primitive recursive and computable sets are closed under complement and set difference
- Partially recursive sets are closed under set difference by Comp sets
- Partially recursive sets are closed under finite symmetric difference
- The finite symmetric difference relation is defined, and is transitive and commutative

## Notation
- '∆' is used for symmetric difference
- '=*' is used to mean that the symmetric difference of two sets is finite

## References
- [R. I. Soare *Turing Computability - Theory and Applications*] [Soare2016]
-/

namespace Computability


/-- The primitive recursive subsets of ℕ are those with primitive recursive characteristic functions -/
def primrec_set (X : Set ℕ) : Prop := ∃ (f : ℕ → Bool), Primrec f ∧ ∀ x, x ∈ X ↔ f x = true

/-- The computable subsets of ℕ are those with primitive recursive characteristic functions -/
def computable_set (X : Set ℕ) : Prop := ∃ (f : ℕ → Bool), Computable f ∧ ∀ x, x ∈ X ↔ f x = true

/-- The partial recursive subsets of ℕ are those with partially recursive characteristic functions -/
def partrec_set (X : Set ℕ) : Prop := ∃ (f: ℕ →. Unit), Partrec f ∧ f.Dom = X

/-! Implications between notions -/
/-- Primitive recursive sets are computable -/
theorem primrec_set.computable (X : Set ℕ) (h : primrec_set X) : computable_set X := by
  obtain ⟨f, ⟨hPrim, hSpec⟩⟩ := h
  use f
  constructor
  · apply Primrec.to_comp
    exact hPrim
  · exact hSpec

/-- Computable sets are partial recursive -/
theorem computable_set.partrec (X : Set ℕ) (h : computable_set X) : partrec_set X := by
  obtain ⟨f, ⟨hComp, hSpec⟩⟩ := h
  apply Computable.partrec at hComp
  let f' : ℕ →. Unit := fun x => bif f x then Part.some () else Part.none
  use f'
  constructor
  · apply Partrec.cond hComp
    exact Partrec.const' (Part.some ())
    exact Partrec.const' (Part.none)
  · ext x
    simp [f']
    rw [Part.dom_iff_mem, hSpec]
    apply Iff.intro
    · intro h
      obtain ⟨y, hy⟩ := h
      cases hfx : f x
      · simp [hfx] at hy
      · rfl
    · intro h
      use ()
      cases hfx : f x
      · simp [hfx]
        rw [h] at hfx
        tauto
      · simp [hfx]

/-- Primitive recursive sets are partial recursive -/
theorem primrec_set.partrec (X : Set ℕ) (h : primrec_set X) : partrec_set X := by
  apply computable_set.partrec
  apply primrec_set.computable
  exact h

/-! ### Lemmata about the natural numbers -/
/-- ℕ is primitive recursive -/
theorem nat_primrec : primrec_set (Set.univ : Set ℕ) := by
  use (fun _ => true)
  constructor
  · apply Primrec.const
  · simp

/-- ℕ is computable -/
theorem nat_computable : computable_set (Set.univ : Set ℕ) := by
  apply primrec_set.computable
  exact nat_primrec

/-- ℕ is partial recursive -/
theorem nat_partrec : partrec_set (Set.univ : Set ℕ) := by
  apply computable_set.partrec
  exact nat_computable

/-! ### Lemmata about the empty set -/
/-- ∅ is primitive recursive -/
theorem empty_primrec_set : primrec_set (∅ : Set ℕ) := by
  use (fun _ => false)
  constructor
  · apply Primrec.const
  · simp

/-- ∅ is computable -/
theorem empty_computable_set : computable_set (∅ : Set ℕ) := by
  apply primrec_set.computable
  exact empty_primrec_set

/-- ∅ is partial recursive -/
theorem empty_partrec_set : partrec_set (∅ : Set ℕ) := by
  apply computable_set.partrec
  exact empty_computable_set


/-! ### Lemmata about singletons -/
/- Singletons are primitive recursive -/
theorem singleton_primrec (a : ℕ) : primrec_set ({a} : Set ℕ) := by
  let f : ℕ → Bool := fun n => bif n = a then true else false
  use f
  constructor
  · apply Primrec.cond
    · apply PrimrecRel.comp
      · exact Primrec.eq
      · exact Primrec.id
      · exact Primrec.const a
    · apply Primrec.const
    · apply Primrec.const
  · intro x
    simp [f]

/- Singletons are computable -/
theorem singleton_computable (a : ℕ) : computable_set ({a} : Set ℕ) := by
  apply primrec_set.computable
  exact singleton_primrec a

/- Singletons are partial recursive -/
theorem singleton_partrec (a : ℕ) : partrec_set ({a} : Set ℕ) := by
  apply computable_set.partrec
  exact singleton_computable a


/-! ### Lemmata about set operations -/

/-! ### Lemmata about unions -/
/-- The primitive recursive sets are closed under union -/
theorem primrec_set.Union (X Y : Set ℕ) (hX : primrec_set X) (hY : primrec_set Y) :
    primrec_set (X ∪ Y) := by
  obtain ⟨f, ⟨fPrim, fSpec⟩⟩ := hX
  obtain ⟨g, ⟨gPrim, gSpec⟩⟩ := hY
  let h : ℕ → Bool := fun (a : ℕ) => f a ∨ g a
  use h
  constructor
  · refine Primrec.ite ?_ ?_ ?_
    · apply PrimrecPred.or
      · apply PrimrecRel.comp
        · exact Primrec.eq
        · exact fPrim
        · exact Primrec.const true
      · apply PrimrecRel.comp
        · exact Primrec.eq
        · exact gPrim
        · exact Primrec.const true
    · exact Primrec.const true
    · exact Primrec.const false
  · intro x
    have hfg : h x = true ↔ (f x = true ∨ g x = true) := by
      exact decide_eq_true_iff
    rw [hfg]
    apply Iff.trans
    exact Set.mem_union x X Y
    rw [fSpec, gSpec]

/-- The computable sets are closed under union -/
theorem computable_set.Union (X Y : Set ℕ) (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X ∪ Y) := by
  obtain ⟨f, ⟨fComp, fSpec⟩⟩ := hX
  obtain ⟨g, ⟨gComp, gSpec⟩⟩ := hY
  let h : ℕ → Bool := fun (a : ℕ) => f a || g a
  use h
  constructor
  · unfold h
    apply Computable.cond fComp (Computable.const true) gComp
  · intro x
    have hfg : h x = true ↔ (f x = true || g x = true) := by
      simp [h]
    rw [hfg]
    apply Iff.trans
    exact Set.mem_union x X Y
    rw [fSpec, gSpec]
    simp

/-- The partial recursive sets are closed under union -/
theorem partrec_set.Union (X Y : Set ℕ) (hX : partrec_set X) (hY : partrec_set Y) :
    partrec_set (X ∪ Y) := by
  obtain ⟨f, ⟨fPrim, fSpec⟩⟩ := hX
  obtain ⟨g, ⟨gPrim, gSpec⟩⟩ := hY
  have hfg : ∃ (h : ℕ →. Unit), -- merge the witnessing functions for Z and {a}
    Partrec h ∧ ∀ (a : ℕ), (∀ x ∈ h a, x ∈ f a ∨ x ∈ g a) ∧
    ((h a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
    apply Partrec.merge' fPrim gPrim
  obtain ⟨h, ⟨hPrim, hSpec⟩⟩ := hfg
  use h
  constructor
  · exact hPrim
  · ext x
    have hx := hSpec x
    rw [← fSpec, ← gSpec]
    exact hx.right


/-! ### Lemmata about intersections -/
/-- The primitive recursive sets are closed under intersection -/
theorem primrec_set.Inter (X Y : Set ℕ) (hX : primrec_set X) (hY : primrec_set Y) :
    primrec_set (X ∩ Y) := by
  obtain ⟨f, ⟨fPrim, fSpec⟩⟩ := hX
  obtain ⟨g, ⟨gPrim, gSpec⟩⟩ := hY
  let h : ℕ → Bool := fun (a : ℕ) => f a ∧ g a
  use h
  constructor
  · refine Primrec.ite ?_ ?_ ?_
    · apply PrimrecPred.and
      · apply PrimrecRel.comp
        · exact Primrec.eq
        · exact fPrim
        · exact Primrec.const true
      · apply PrimrecRel.comp
        · exact Primrec.eq
        · exact gPrim
        · exact Primrec.const true
    · exact Primrec.const true
    · exact Primrec.const false
  · intro x
    have hfg : h x = true ↔ (f x = true ∧ g x = true) := by
      exact decide_eq_true_iff
    rw [hfg]
    apply Iff.trans
    apply Set.mem_inter_iff
    rw [fSpec, gSpec]

/-- The computable sets are closed under intersection -/
theorem computable_set.Inter (X Y : Set ℕ) (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X ∩ Y) := by
  obtain ⟨f, ⟨fComp, fSpec⟩⟩ := hX
  obtain ⟨g, ⟨gComp, gSpec⟩⟩ := hY
  let h : ℕ → Bool := fun (a : ℕ) => f a ∧ g a
  use h
  constructor
  · unfold h
    simp
    refine Computable₂.comp ?_ fComp gComp
    apply Primrec₂.to_comp ?_
    exact Primrec.and
  · intro x
    have hfg : h x = true ↔ (f x = true ∧ g x = true) := by
      simp [h]
    rw [hfg]
    apply Iff.trans
    exact Set.mem_inter_iff x X Y
    rw [fSpec, gSpec]

/-- The partial recursive sets are closed under intersection -/
theorem partrec_set.Inter (X Y : Set ℕ) (hX : partrec_set X) (hY : partrec_set Y) :
    partrec_set (X ∩ Y) := by
  obtain ⟨f, ⟨fPart, fSpec⟩⟩ := hX
  obtain ⟨g, ⟨gPart, gSpec⟩⟩ := hY
  let h := fun x => (f x).bind (fun _ => g x)
  use h
  constructor
  · apply Partrec.bind
    · exact fPart
    · exact Partrec.comp gPart (Computable.fst)
  · ext x
    rw [← fSpec, ← gSpec]
    simp [h]
    apply and_congr
    · exact Part.dom_iff_mem
    · exact Part.dom_iff_mem


/-! ### Lemmata about complements
Note that unlike the other notions, primitive recursive sets are *not* closed under complement -/
/-- The primitive recursive sets are closed under complement -/
theorem primrec_set.Compl (X : Set ℕ) (hX : primrec_set X) : primrec_set Xᶜ := by
  obtain ⟨f, ⟨fPrim, fSpec⟩⟩ := hX
  let f' := fun x => !(f x)
  use f'
  constructor
  · refine Primrec.cond fPrim ?_ ?_
    · exact Primrec.const false
    · exact Primrec.const true
  · intro x
    simp [fSpec, f']

/-- A set is primitive recursive iff its complement is -/
theorem primrec_set.Compl_iff (X : Set ℕ) : primrec_set X ↔ primrec_set Xᶜ := by
  constructor
  · exact primrec_set.Compl X
  · intro h
    rw [← compl_compl X]
    apply primrec_set.Compl Xᶜ
    exact h

/-- The computable sets are closed under complement -/
theorem computable_set.Compl (X : Set ℕ) (hX : computable_set X) : computable_set Xᶜ := by
  obtain ⟨f, ⟨fComp, fSpec⟩⟩ := hX
  use fun x => !(f x)
  constructor
  · refine Computable.cond fComp ?_ ?_
    · exact Computable.const false
    · exact Computable.const true
  · intro x
    simp [fSpec]

/-- A set is computable iff its complement is -/
theorem computable_set.Compl_iff (X : Set ℕ) : computable_set X ↔ computable_set Xᶜ := by
  constructor
  · exact computable_set.Compl X
  · intro h
    rw [← compl_compl X]
    apply computable_set.Compl Xᶜ
    exact h


/-! ### Lemmata about set differences
Note that primitive recursive sets are only closed under set difference by computable sets -/
/-- The primitive recursive sets are closed under set difference -/
theorem primrec_set.Sdiff (X Y : Set ℕ) (hX : primrec_set X) (hY : primrec_set Y) :
primrec_set (X \ Y) := by
  apply primrec_set.Compl at hY
  apply primrec_set.Inter
  · exact hX
  · exact hY

/-- The computable sets are closed under set difference -/
theorem computable_set.Sdiff (X Y : Set ℕ) (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X \ Y) := by
  apply computable_set.Compl at hY
  apply computable_set.Inter
  · exact hX
  · exact hY

/-- The partial recursive sets are closed under set difference *by computable sets* -/
theorem partrec_set.Sdiff_computable (X Y : Set ℕ) (hX : partrec_set X) (hY : computable_set Y) :
    partrec_set (X \ Y) := by
  apply computable_set.Compl at hY
  apply partrec_set.Inter
  · exact hX
  · apply computable_set.partrec
    exact hY


/-! ### Lemmata about finite sets -/
/-- Finite sets are primitive recursive -/
theorem finite_primrec_set (X : Set ℕ) (h : X.Finite) : primrec_set X := by
  obtain ⟨X, rfl⟩ := Set.Finite.exists_finset_coe h
  induction' X using Finset.induction_on' with a S ha hS haS hSPrim
  · simp
    exact empty_primrec_set
  · rw [Finset.coe_insert]
    rw [Set.insert_eq]
    apply primrec_set.Union
    · exact singleton_primrec a
    · apply hSPrim
      exact Finite.of_fintype ↑↑S

/-- Finite sets are comptuable -/
theorem finite_computable_set (X : Set ℕ) (h : X.Finite) : computable_set X := by
  apply primrec_set.computable
  apply finite_primrec_set
  exact h

/-- Finite sets are partial recursive -/
theorem finite_partrec_set (X : Set ℕ) (h : X.Finite) : partrec_set X := by
  apply computable_set.partrec
  apply finite_computable_set
  exact h


/-! ### Lemmata about cofinite sets -/
/-- Cofinite sets are primitive recursive -/
theorem cofinite_primrec_set (X : Set ℕ) (hX : Xᶜ.Finite) : primrec_set X := by
  obtain ⟨Xc, hXc⟩ := Set.Finite.exists_finset_coe hX
  rw [← compl_compl X]
  apply primrec_set.Compl
  let Yc : Finset ℕ := hX.toFinset
  rw [← hXc]
  apply finite_primrec_set
  exact Finite.of_fintype ↑↑Xc

/-- Cofinite sets are comptuable -/
theorem cofinite_computable_set (X : Set ℕ) (hX : Xᶜ.Finite) : computable_set X := by
  apply primrec_set.computable
  apply cofinite_primrec_set
  exact hX

/-- Cofinite sets are partial recursive -/
theorem cofinite_partrec_set (X : Set ℕ) (hX : Xᶜ.Finite) : partrec_set X := by
  apply computable_set.partrec
  apply cofinite_computable_set
  exact hX


/-! ### Lemmata about symmetric differences -/
infixl:100 " ∆ " => symmDiff
/-- The primitive recursive sets are closed under symmetric difference -/
theorem primrec_set.Symmdiff (X Y : Set ℕ) (hX : primrec_set X) (hY : primrec_set Y) :
    primrec_set (X ∆ Y) := by
  rw [Set.symmDiff_def]
  apply primrec_set.Union
  · apply primrec_set.Sdiff
    · exact hX
    · exact hY
  · apply primrec_set.Sdiff
    · exact hY
    · exact hX

/-- The computable sets are closed under symmetric difference -/
theorem computable_set.Symmdiff (X Y : Set ℕ) (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X ∆ Y) := by
  rw [Set.symmDiff_def]
  apply computable_set.Union
  · apply computable_set.Sdiff
    · exact hX
    · exact hY
  · apply computable_set.Sdiff
    · exact hY
    · exact hX


/-! ### Lemmata about finite symmetric differences -/
def eq_star (X Y : Set ℕ) : Prop := (X∆Y).Finite
infix:50 " =* " => eq_star
/-- The relation of having a finite symmetric difference is commutative -/
theorem eq_star_comm (X Y : Set ℕ) : X =* Y ↔ Y =* X := by
unfold eq_star
rw [symmDiff_comm]

/-- The relation of having a finite symmetric difference is transitive -/
theorem eq_star_trans (X Y Z : Set ℕ) (hXY : X =* Y) (hYZ : Y =* Z) : X =* Z := by
  unfold eq_star
  exact (Set.Finite.symmDiff_congr hXY).mpr hYZ

/-- If X=*Y and X is finite, then Y is finite -/
theorem finite_eq_star (X Y : Set ℕ) (hXY : X =* Y) (hX : X.Finite): Y.Finite := by
  unfold eq_star at hXY
  rw [Set.symmDiff_def, Set.finite_union] at hXY
  obtain ⟨hXY, hYX⟩ := hXY
  have hY : Y = (Y∩X)∪(Y\X) := by rw [Set.inter_union_diff]
  rw [hY]
  rw [Set.finite_union]
  constructor
  · exact Set.Finite.inter_of_right hX Y
  · exact hYX

/-- If X=*Y, then X is finite iff Y is -/
theorem finite_eq_star_iff (X Y : Set ℕ) (hXY : X =* Y) : X.Finite ↔ Y.Finite := by
  constructor
  · intro h
    apply finite_eq_star X
    exact hXY
    exact h
  · intro h
    apply finite_eq_star Y
    rw [eq_star_comm]
    exact hXY
    exact h

/-- If X=*Y and X is infinite, then Y is infinite -/
theorem infinite_eq_star (X Y : Set ℕ) (hXY : X =* Y) (hX : X.Infinite) : Y.Infinite := by
  by_contra hY
  simp at hY
  revert hX
  simp
  apply finite_eq_star Y
  rw [eq_star_comm]
  exact hXY
  exact hY

/-- If X=*Y, then X is infinite iff Y is -/
theorem infinite_eq_star_iff (X Y : Set ℕ) (hXY : X =* Y) : X.Infinite ↔ Y.Infinite := by
  constructor
  · exact fun a ↦ infinite_eq_star X Y hXY a
  · rw [eq_star_comm] at hXY
    exact fun a ↦ infinite_eq_star Y X hXY a

/-- If X=*Y, then Xᶜ=*Yᶜ -/
theorem compl_eq_star (X Y : Set ℕ) (hXY : X =* Y) : Xᶜ =* Yᶜ := by
  unfold eq_star
  unfold eq_star at hXY
  revert hXY
  simp

/-- If X=*Y and X is partial recursive, then Y is partial recursive -/
theorem partrec_set_eq_star (X Y : Set ℕ) (hXY : X =* Y) : partrec_set X → partrec_set Y := by
  let S : Finset ℕ := hXY.toFinset
  have hS : ↑S = (X∆Y) := Set.Finite.coe_toFinset hXY
  let C := Y\X
  let D := X\Y
  have hC : C.Finite := by
    apply Finite.Set.subset S
    simp [S, C, Set.symmDiff_def]
  let FC : Finset ℕ := hC.toFinset
  have hFC : ↑FC = C := Set.Finite.coe_toFinset hC
  have hD : D.Finite := by
    apply Finite.Set.subset S
    simp [S, D, Set.symmDiff_def]
  let FD : Finset ℕ := hD.toFinset
  have hFD : ↑FD = D := Set.Finite.coe_toFinset hD
  have hY : Y = (X∪FC)\FD := by
    simp [C, FC, D, FD]
    rw [Set.diff_diff_right, Set.union_inter_cancel_right, Set.union_diff_distrib]
    simp
    rw [Set.union_eq_self_of_subset_left]
    exact Set.diff_subset
  rw [hY]
  intro hX
  apply partrec_set.Sdiff_computable
  · apply partrec_set.Union
    · exact hX
    · apply finite_partrec_set FC
      exact Finite.of_fintype ↑↑FC
  · apply finite_computable_set FD
    exact Finite.of_fintype ↑↑FD

/-- If X=*Y, then X is partial recursive iff Y is -/
theorem partrec_set_eq_star_iff (X Y : Set ℕ) (hXY : X =* Y) : partrec_set X ↔ partrec_set Y := by
  constructor
  · exact fun a ↦ partrec_set_eq_star X Y hXY a
  · rw [eq_star_comm] at hXY
    exact fun a ↦ partrec_set_eq_star Y X hXY a

end Computability
