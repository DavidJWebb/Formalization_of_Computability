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

open Set Finite

namespace Computability

variable (X Y : Set ℕ)

/-- Primitive recursive subsets of ℕ are those with primitive recursive characteristic functions -/
def primrec_set : Prop := ∃ (f : ℕ → Bool), Primrec f ∧ ∀ x, x ∈ X ↔ f x = true

/-- Computable subsets of ℕ are those with computable characteristic functions -/
def computable_set : Prop := ∃ (f : ℕ → Bool), Computable f ∧ ∀ x, x ∈ X ↔ f x = true

/-- Partial recursive subsets of ℕ are those with partially recursive characteristic functions -/
def partrec_set : Prop := ∃ (f: ℕ →. Unit), Partrec f ∧ f.Dom = X

/-! Implications between notions -/
/-- Primitive recursive sets are computable -/
theorem primrec_set.computable (h : primrec_set X) : computable_set X := by
  obtain ⟨f, ⟨_, _⟩⟩ := h
  use f
  simp_all [Primrec.to_comp]

/-- Computable sets are partial recursive -/
theorem computable_set.partrec (h : computable_set X) : partrec_set X := by
  obtain ⟨f, ⟨fComp, _⟩⟩ := h
  apply Computable.partrec at fComp
  use fun x ↦ bif f x then Part.some () else Part.none
  constructor
  · exact Partrec.cond fComp (Partrec.const' (Part.some ())) (Partrec.const' (Part.none))
  · ext x
    cases hfx : f x <;> simp_all

/-- Primitive recursive sets are partial recursive -/
theorem primrec_set.partrec (h : primrec_set X) : partrec_set X := by
  apply computable_set.partrec
  apply primrec_set.computable
  exact h

/-! ### Lemmata about the natural numbers -/
/-- ℕ is primitive recursive -/
theorem nat_primrec : primrec_set (univ : Set ℕ) := by
  use (fun _ ↦ true)
  simp_all [Primrec.const]

/-- ℕ is computable -/
theorem nat_computable : computable_set (univ : Set ℕ) := by
  apply primrec_set.computable
  exact nat_primrec

/-- ℕ is partial recursive -/
theorem nat_partrec : partrec_set (univ : Set ℕ) := by
  apply computable_set.partrec
  exact nat_computable

/-! ### Lemmata about the empty set -/
/-- ∅ is primitive recursive -/
theorem empty_primrec_set : primrec_set (∅ : Set ℕ) := by
  use (fun _ ↦ false)
  simp_all [Primrec.const]

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
  use fun n ↦ bif n = a then true else false
  constructor
  · apply Primrec.cond ?_ (Primrec.const true) (Primrec.const false)
    · exact PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const a)
  · simp

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
theorem primrec_set.Union (hX : primrec_set X) (hY : primrec_set Y) :
    primrec_set (X ∪ Y) := by
  obtain ⟨f, ⟨fPrim, hX⟩⟩ := hX
  obtain ⟨g, ⟨gPrim, hY⟩⟩ := hY
  use fun (a : ℕ) ↦ f a ∨ g a
  constructor
  · apply Primrec.ite ?_ (Primrec.const true) (Primrec.const false)
    · apply PrimrecPred.or
      · exact PrimrecRel.comp Primrec.eq fPrim (Primrec.const true)
      · exact PrimrecRel.comp Primrec.eq gPrim (Primrec.const true)
  · intro x
    apply Iff.trans
    · exact mem_union x X Y
    · simp [hX, hY]

/-- The computable sets are closed under union -/
theorem computable_set.Union (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X ∪ Y) := by
  obtain ⟨f, ⟨fComp, hX⟩⟩ := hX
  obtain ⟨g, ⟨gComp, hY⟩⟩ := hY
  use fun (a : ℕ) ↦ f a || g a
  constructor
  · exact Computable.cond fComp (Computable.const true) gComp
  · intro x
    apply Iff.trans
    · exact mem_union x X Y
    · simp [hX, hY]

/-- The partial recursive sets are closed under union -/
theorem partrec_set.Union (hX : partrec_set X) (hY : partrec_set Y) :
    partrec_set (X ∪ Y) := by
  obtain ⟨f, ⟨fPrim, hX⟩⟩ := hX
  obtain ⟨g, ⟨gPrim, hY⟩⟩ := hY
  obtain ⟨h, ⟨hPrim, hfg⟩⟩ := Partrec.merge' fPrim gPrim
  use h
  constructor
  · exact hPrim
  · ext x
    rw [← hX, ← hY]
    exact (hfg x).right


/-! ### Lemmata about intersections -/
/-- The primitive recursive sets are closed under intersection -/
theorem primrec_set.Inter (hX : primrec_set X) (hY : primrec_set Y) :
    primrec_set (X ∩ Y) := by
  obtain ⟨f, ⟨fPrim, hX⟩⟩ := hX
  obtain ⟨g, ⟨gPrim, hY⟩⟩ := hY
  use fun (a : ℕ) ↦ f a ∧ g a
  constructor
  · apply Primrec.ite (PrimrecPred.and ?_ ?_) (Primrec.const true) (Primrec.const false)
    · exact PrimrecRel.comp Primrec.eq fPrim (Primrec.const true)
    · exact PrimrecRel.comp Primrec.eq gPrim (Primrec.const true)
  · intro x
    apply Iff.trans
    · apply mem_inter_iff
    · simp [hX, hY]

/-- The computable sets are closed under intersection -/
theorem computable_set.Inter (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X ∩ Y) := by
  obtain ⟨f, ⟨fComp, hX⟩⟩ := hX
  obtain ⟨g, ⟨gComp, hY⟩⟩ := hY
  use fun (a : ℕ) ↦ f a ∧ g a
  constructor
  · simp only [Bool.decide_and, Bool.decide_eq_true]
    exact Computable₂.comp (Primrec₂.to_comp Primrec.and) fComp gComp
  · intro x
    apply Iff.trans
    · exact mem_inter_iff x X Y
    · simp [hX, hY]

/-- The partial recursive sets are closed under intersection -/
theorem partrec_set.Inter (hX : partrec_set X) (hY : partrec_set Y) :
    partrec_set (X ∩ Y) := by
  obtain ⟨f, ⟨fPart, hX⟩⟩ := hX
  obtain ⟨g, ⟨gPart, hY⟩⟩ := hY
  use fun x ↦ (f x).bind (fun _ ↦ g x)
  constructor
  · exact Partrec.bind fPart (Partrec.comp gPart (Computable.fst))
  · ext x
    simp [← hX, ← hY]
    apply and_congr <;> exact Part.dom_iff_mem


/-! ### Lemmata about complements
Note that unlike the other notions, partial recursive sets are *not* closed under complement -/
/-- The primitive recursive sets are closed under complement -/
theorem primrec_set.Compl (hX : primrec_set X) : primrec_set Xᶜ := by
  obtain ⟨f, ⟨fPrim, hX⟩⟩ := hX
  use fun x ↦ !(f x)
  constructor
  · exact Primrec.cond fPrim (Primrec.const false) (Primrec.const true)
  · simp [hX]

/-- A set is primitive recursive iff its complement is -/
theorem primrec_set.Compl_iff : primrec_set X ↔ primrec_set Xᶜ := by
  constructor
  · exact primrec_set.Compl X
  · intro h
    rw [← compl_compl X]
    apply primrec_set.Compl Xᶜ
    exact h

/-- The computable sets are closed under complement -/
theorem computable_set.Compl (hX : computable_set X) : computable_set Xᶜ := by
  obtain ⟨f, ⟨fComp, hX⟩⟩ := hX
  use fun x ↦ !(f x)
  constructor
  · exact Computable.cond fComp (Computable.const false) (Computable.const true)
  · simp [hX]

/-- A set is computable iff its complement is -/
theorem computable_set.Compl_iff : computable_set X ↔ computable_set Xᶜ := by
  constructor
  · exact computable_set.Compl X
  · intro h
    rw [← compl_compl X]
    apply computable_set.Compl Xᶜ
    exact h


/-! ### Lemmata about set differences
Note that primitive recursive sets are only closed under set difference by computable sets -/
/-- The primitive recursive sets are closed under set difference -/
theorem primrec_set.Sdiff (hX : primrec_set X) (hY : primrec_set Y) :
primrec_set (X \ Y) := by
  apply primrec_set.Compl at hY
  apply primrec_set.Inter
  · exact hX
  · exact hY

/-- The computable sets are closed under set difference -/
theorem computable_set.Sdiff (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X \ Y) := by
  apply computable_set.Compl at hY
  apply computable_set.Inter
  · exact hX
  · exact hY

/-- The partial recursive sets are closed under set difference *by computable sets* -/
theorem partrec_set.Sdiff_computable (hX : partrec_set X) (hY : computable_set Y) :
    partrec_set (X \ Y) := by
  apply computable_set.Compl at hY
  apply partrec_set.Inter
  · exact hX
  · apply computable_set.partrec
    exact hY


/-! ### Lemmata about finite sets -/
/-- Finite sets are primitive recursive -/
theorem finite_primrec_set (h : X.Finite) : primrec_set X := by
  obtain ⟨X, rfl⟩ := exists_finset_coe h
  induction' X using Finset.induction_on' with a S ha hS haS hSPrim
  · simp only [Finset.coe_empty]
    exact empty_primrec_set
  · rw [Finset.coe_insert]
    rw [insert_eq]
    apply primrec_set.Union
    · exact singleton_primrec a
    · apply hSPrim
      exact of_fintype ↑↑S

/-- Finite sets are comptuable -/
theorem finite_computable_set (h : X.Finite) : computable_set X := by
  apply primrec_set.computable
  apply finite_primrec_set
  exact h

/-- Finite sets are partial recursive -/
theorem finite_partrec_set (h : X.Finite) : partrec_set X := by
  apply computable_set.partrec
  apply finite_computable_set
  exact h


/-! ### Lemmata about cofinite sets -/
/-- Cofinite sets are primitive recursive -/
theorem cofinite_primrec_set (hX : Xᶜ.Finite) : primrec_set X := by
  obtain ⟨Xc, hXc⟩ := exists_finset_coe hX
  rw [← compl_compl X]
  apply primrec_set.Compl
  rw [← hXc]
  apply finite_primrec_set
  exact Finset.finite_toSet Xc

/-- Cofinite sets are comptuable -/
theorem cofinite_computable_set (hX : Xᶜ.Finite) : computable_set X := by
  apply primrec_set.computable
  apply cofinite_primrec_set
  exact hX

/-- Cofinite sets are partial recursive -/
theorem cofinite_partrec_set (hX : Xᶜ.Finite) : partrec_set X := by
  apply computable_set.partrec
  apply cofinite_computable_set
  exact hX


/-! ### Lemmata about symmetric differences -/
infixl:100 " ∆ " => symmDiff
/-- The primitive recursive sets are closed under symmetric difference -/
theorem primrec_set.Symmdiff (hX : primrec_set X) (hY : primrec_set Y) :
    primrec_set (X ∆ Y) := by
  rw [symmDiff_def]
  apply primrec_set.Union
  <;> apply primrec_set.Sdiff
  <;> simp [hX, hY]

/-- The computable sets are closed under symmetric difference -/
theorem computable_set.Symmdiff (hX : computable_set X) (hY : computable_set Y) :
    computable_set (X ∆ Y) := by
  rw [symmDiff_def]
  apply computable_set.Union
  <;> apply computable_set.Sdiff
  <;> simp [hX, hY]


/-! ### Lemmata about finite symmetric differences -/
def eq_star (X Y : Set ℕ) : Prop := (X∆Y).Finite
infix:50 " =* " => eq_star
/-- The relation of having a finite symmetric difference is commutative -/
theorem eq_star_comm : X =* Y ↔ Y =* X := by
unfold eq_star
rw [symmDiff_comm]

/-- The relation of having a finite symmetric difference is transitive -/
theorem eq_star_trans (X Y Z : Set ℕ) (hXY : X =* Y) (hYZ : Y =* Z) : X =* Z := by
  unfold eq_star
  exact (symmDiff_congr hXY).mpr hYZ

/-- If X=*Y and X is finite, then Y is finite -/
theorem finite_eq_star (hXY : X =* Y) (hX : X.Finite): Y.Finite := by
  unfold eq_star at hXY
  rw [Set.symmDiff_def, finite_union] at hXY
  obtain ⟨_, hYX⟩ := hXY
  have hY : Y = (Y∩X) ∪ (Y\X) := by rw [inter_union_diff]
  rw [hY, finite_union]
  constructor
  · exact inter_of_right hX Y
  · exact hYX

/-- If X=*Y, then X is finite iff Y is -/
theorem finite_eq_star_iff (hXY : X =* Y) : X.Finite ↔ Y.Finite := by
  constructor
  · intro h
    apply finite_eq_star X
    · exact hXY
    · exact h
  · intro h
    apply finite_eq_star Y
    rw [eq_star_comm]
    · exact hXY
    · exact h

/-- If X=*Y and X is infinite, then Y is infinite -/
theorem infinite_eq_star (hXY : X =* Y) (hX : X.Infinite) : Y.Infinite := by
  by_contra hY
  simp at hY
  revert hX
  simp only [imp_false, Set.not_infinite]
  apply finite_eq_star Y
  rw [eq_star_comm]
  · exact hXY
  · exact hY

/-- If X=*Y, then X is infinite iff Y is -/
theorem infinite_eq_star_iff (hXY : X =* Y) : X.Infinite ↔ Y.Infinite := by
  constructor
  · exact fun a ↦ infinite_eq_star X Y hXY a
  · rw [eq_star_comm] at hXY
    exact fun a ↦ infinite_eq_star Y X hXY a

/-- If X=*Y, then Xᶜ=*Yᶜ -/
theorem compl_eq_star (hXY : X =* Y) : Xᶜ =* Yᶜ := by
  revert hXY
  unfold eq_star
  simp

/-- If X=*Y and X is partial recursive, then Y is partial recursive -/
theorem partrec_set_eq_star (hXY : X =* Y) : partrec_set X → partrec_set Y := by
  intro hX
  let S : Finset ℕ := hXY.toFinset
  have hS : ↑S = (X∆Y) := Finite.coe_toFinset hXY
  let C := Y\X
  let D := X\Y
  have hY : Y = (X∪C)\D := by
    simp only [C, D, S, union_diff_self, diff_diff_right, union_inter_cancel_right,
      union_diff_distrib, sdiff_self, bot_eq_empty, empty_union]
    rw [union_eq_self_of_subset_left]
    exact diff_subset
  rw [hY]
  apply partrec_set.Sdiff_computable
  · apply partrec_set.Union
    · exact hX
    · apply finite_partrec_set C
      apply Set.subset S
      simp [S, C, symmDiff_def]
  · apply finite_computable_set D
    apply Set.subset S
    simp [S, D, Set.symmDiff_def]

/-- If X=*Y, then X is partial recursive iff Y is -/
theorem partrec_set_eq_star_iff (hXY : X =* Y) : partrec_set X ↔ partrec_set Y := by
  constructor
  · exact fun a ↦ partrec_set_eq_star X Y hXY a
  · rw [eq_star_comm] at hXY
    exact fun a ↦ partrec_set_eq_star Y X hXY a

end Computability
