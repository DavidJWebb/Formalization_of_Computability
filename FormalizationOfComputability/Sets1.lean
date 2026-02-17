/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import Mathlib.Computability.Halting
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Preorder.Finite

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

def eq_star (X Y : Set ℕ) : Prop := (symmDiff X Y).Finite -- X =ᶠ[Filter.cofinite α] Y
infixl:100 " ∆ " => symmDiff
infix:50 " =* " => eq_star

-- TODO: find a better place for these

open Set

variable {X Y : Set ℕ}

/-- The relation of having a finite symmetric difference is commutative -/
theorem eq_star_comm : X =* Y ↔ Y =* X := by simp [eq_star, symmDiff_comm]

/-- The relation of having a finite symmetric difference is transitive -/
theorem eq_star_trans (X Y Z : Set ℕ) (hXY : X =* Y) (hYZ : Y =* Z) : X =* Z :=
  (Finite.symmDiff_congr hXY).mpr hYZ

/-- If X=*Y and X is finite, then Y is finite -/
theorem finite_eq_star (hXY : X =* Y) (hX : X.Finite): Y.Finite := by
  unfold eq_star at hXY
  rw [Set.symmDiff_def, finite_union] at hXY
  rw [← (inter_union_diff Y X), finite_union]
  constructor
  · exact Finite.inter_of_right hX Y
  · exact hXY.right

/-- If X=*Y, then X is finite iff Y is -/
theorem finite_eq_star_iff (hXY : X =* Y) : X.Finite ↔ Y.Finite := by
  constructor
  <;> intro h
  · exact finite_eq_star hXY h
  · rw [eq_star_comm] at hXY
    exact finite_eq_star (hXY) h

/-- If X=*Y and X is infinite, then Y is infinite -/
theorem infinite_eq_star (hXY : X =* Y) (hX : X.Infinite) : Y.Infinite := by
  by_contra hY
  simp only [Set.not_infinite] at hY
  revert hX
  simp only [imp_false, Set.not_infinite]
  exact finite_eq_star (eq_star_comm.mp hXY) hY

/-- If X=*Y, then X is infinite iff Y is -/
theorem infinite_eq_star_iff (hXY : X =* Y) : X.Infinite ↔ Y.Infinite := by
  constructor
  · exact infinite_eq_star hXY
  · exact infinite_eq_star (eq_star_comm.mp hXY)

/-- If X=*Y, then Xᶜ=*Yᶜ -/
theorem compl_eq_star (hXY : X =* Y) : Xᶜ =* Yᶜ := by
  revert hXY
  simp [eq_star]

namespace Primrec

open Primrec

/-- Primitive recursive subsets of ℕ are those with primitive recursive characteristic functions -/
def set (X : Set ℕ) [DecidablePred fun x ↦ x ∈ X] : Prop := PrimrecPred (λ x ↦ x ∈ X)

variable {X Y : Set ℕ} [DecidablePred fun x ↦ x ∈ X] [DecidablePred fun y ↦ y ∈ Y]

/-- This definition is equivalent to the textbook definition. -/
theorem set_iff_exists  : set X ↔ (∃ (f : ℕ → Bool), Primrec f ∧ ∀ x, x ∈ X ↔ f x = true) := by
  constructor
  <;> intro h
  · use λ x ↦ (x ∈ X) = true
    simp only [eq_iff_iff, iff_true, decide_eq_true_eq, implies_true, and_true]
    exact h
  · obtain ⟨f, ⟨hf, h⟩⟩ := h
    simp only [set, PrimrecPred]
    refine Primrec.of_eq hf ?_
    intro x
    refine Bool.coe_iff_coe.mp ?_
    simp only [decide_eq_true_eq]
    rw [← h x]

/-- ℕ is primitive recursive -/
theorem nat : set (univ : Set ℕ) := const (decide True)

/-- ∅ is primitive recursive -/
theorem empty_set : set (∅ : Set ℕ) := by
  simp only [set, PrimrecPred]
  exact const false

/- Singletons are primitive recursive -/
theorem singleton (a : ℕ) : set ({a} : Set ℕ) := PrimrecRel.comp .eq .id (.const a)

/-- The primitive recursive sets are closed under union -/
theorem union (hX : set X) (hY : set Y) : set (X ∪ Y) := by
  apply PrimrecPred.of_eq (PrimrecPred.or hX hY) (fun a ↦ Iff.symm (mem_union a X Y))

/-- The primitive recursive sets are closed under complement -/
theorem compl (hX : set X) : set Xᶜ := by
  apply PrimrecPred.of_eq (PrimrecPred.not hX) (fun a ↦ Iff.symm (mem_compl_iff X a))

/-- A set is primitive recursive iff its complement is -/
theorem compl_iff : set X ↔ set Xᶜ := by
  constructor
  · exact compl
  · intro h
    apply compl at h
    simp only [compl_compl] at h
    exact h

/-- The primitive recursive sets are closed under intersection -/
theorem inter (hX : set X) (hY : set Y) : set (X ∩ Y) := by
  apply PrimrecPred.of_eq (PrimrecPred.and hX hY) (fun a ↦ Iff.symm (mem_inter_iff a X Y))

/-- The primitive recursive sets are closed under set difference -/
theorem sdiff (hX : set X) (hY : set Y) : set (X \ Y) := by apply inter hX (compl hY)

/-- Finite sets are primitive recursive -/
theorem finite (h : X.Finite) : set X := by
  refine set_iff_exists.mpr ?_
  obtain ⟨X, rfl⟩ := Finite.exists_finset_coe h
  induction' X using Finset.induction_on' with a S _ _ ha hPrim
  · exact set_iff_exists.mp empty_set
  · simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe]
    obtain ⟨f, h1⟩ := hPrim (Finset.finite_toSet S)
    use λ x ↦ (f x || x = a)
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · refine cond h1.left (const true) (ite ?_ (const true) (const false))
      exact PrimrecRel.comp .eq .id (const a)
    · intro x
      by_cases h2 : x = a
      <;> simp_all

/-- Cofinite sets are primitive recursive -/
theorem cofinite (hX : Xᶜ.Finite) : set X := compl_iff.mpr (finite hX)

/-- The primitive recursive sets are closed under symmetric difference -/
theorem symmdiff (hX : set X) (hY : set Y) [DecidablePred fun x ↦ x ∈ X ∆ Y] : set (X ∆ Y) := by
  refine set_iff_exists.mpr ?_
  rw [symmDiff_def]
  use λ x ↦ (x ∈ (X ∩ Yᶜ) ∪ (Y ∩ Xᶜ))
  simp
  refine cond (Primrec₂.comp .and hX ?_) (const true) (Primrec₂.comp .and hY ?_)
  exact cond hY (const false) (const true)
  exact cond hX (const false) (const true)

end Primrec

namespace Computable

open Computable

/-- Computable subsets of ℕ are those with computable characteristic functions -/
def set (X : Set ℕ) : Prop := ∃ (f : ℕ → Bool), Computable f ∧ ∀ x, x ∈ X ↔ f x = true

/-- Primitive recursive sets are computable -/
theorem primrec [DecidablePred λ x ↦ x ∈ X] (h : Primrec.set X) : set X := by
  apply Primrec.set_iff_exists.mp at h
  obtain ⟨f, ⟨_, _⟩⟩ := h
  use f
  simp_all [Primrec.to_comp]

/-- The computable sets are closed under union -/
theorem union (hX : set X) (hY : set Y) : set (X ∪ Y) := by
  obtain ⟨f, ⟨fComp, hX⟩⟩ := hX
  obtain ⟨g, ⟨gComp, hY⟩⟩ := hY
  use fun (a : ℕ) ↦ f a || g a
  constructor
  · exact .cond fComp (.const true) gComp
  · intro x
    apply Iff.trans (mem_union x X Y)
    simp [hX, hY]

/-- The computable sets are closed under complement -/
theorem compl (hX : set X) : set Xᶜ := by
  obtain ⟨f, ⟨fComp, hX⟩⟩ := hX
  use fun x ↦ !(f x)
  constructor
  · exact .cond fComp (.const false) (.const true)
  · simp [hX]

/-- A set is computable iff its complement is -/
theorem compl_iff : set X ↔ set Xᶜ := by
  constructor
  · exact compl
  · rw [← compl_compl X, compl_compl]
    exact compl

/-- The computable sets are closed under intersection -/
theorem inter (hX : set X) (hY : set Y) : set (X ∩ Y) := by
  rw [← compl_compl X, ← compl_compl Y, ← compl_union]
  refine compl (union (compl hX) (compl hY))

/-- The computable sets are closed under set difference -/
theorem sdiff (hX : set X) (hY : set Y) : set (X \ Y) := inter hX (compl hY)

/-- The computable sets are closed under symmetric difference -/
theorem symmdiff (hX : set X) (hY : set Y) : set (X ∆ Y) := by
  rw [symmDiff_def]
  apply union
  <;> simp [sdiff, hX, hY]

end Computable

namespace Partrec

open Partrec

/-- Partial recursive subsets of ℕ are those with partially recursive characteristic functions -/
def set (X : Set ℕ): Prop := ∃ (f: ℕ →. Unit), Partrec f ∧ f.Dom = X

/-- Computable sets are partial recursive -/
theorem computable (h : Computable.set X) : set X := by
  obtain ⟨f, ⟨fComp, _⟩⟩ := h
  use fun x ↦ bif f x then Part.some () else Part.none
  constructor
  · exact .cond (Computable.partrec fComp) (.const' (Part.some ())) (.const' (Part.none))
  · ext x
    cases hfx : f x <;> simp_all

/-- The partial recursive sets are closed under union -/
theorem union (hX : set X) (hY : set Y) : set (X ∪ Y) := by
  obtain ⟨f, ⟨fPart, hX⟩⟩ := hX
  obtain ⟨g, ⟨gPart, hY⟩⟩ := hY
  obtain ⟨h, ⟨hPart, hfg⟩⟩ := Partrec.merge' fPart gPart
  use h
  constructor
  · exact hPart
  · ext x
    rw [← hX, ← hY]
    exact (hfg x).right

-- Note that unlike the other notions, partial recursive sets are *not* closed under complement

/-- The partial recursive sets are closed under intersection. -/
theorem inter (hX : set X) (hY : set Y) : set (X ∩ Y) := by
  obtain ⟨f, ⟨fPart, hX⟩⟩ := hX
  obtain ⟨g, ⟨gPart, hY⟩⟩ := hY
  use fun x ↦ (f x).bind (fun _ ↦ g x)
  constructor
  · exact .bind fPart (Partrec.comp gPart (.fst))
  · ext x
    simp [← hX, ← hY]
    apply and_congr <;> exact Part.dom_iff_mem

/-- The partial recursive sets are closed under set difference *by computable sets*. In general,
the set difference of two partial recursive sets need not be partial recurive. -/
theorem Sdiff_by_computable (hX : set X) (hY : Computable.set Y) : set (X \ Y) :=
  inter hX (computable (Computable.compl hY))

/-- If X=*Y and X is partial recursive, then Y is partial recursive -/
theorem partrec_set_eq_star (hXY : X =* Y) (hX : set X) : set Y := by
  have hY : Y = (X ∪ (Y\X))\(X\Y) := by
    simp only [union_diff_self, diff_diff_right, union_inter_cancel_right,
      union_diff_distrib, sdiff_self, bot_eq_empty, empty_union]
    rw [union_eq_self_of_subset_left]
    exact diff_subset
  rw [hY]
  apply Sdiff_by_computable
  · apply union hX (computable (Computable.primrec (Primrec.finite (Finite.Set.subset hXY.toFinset ?_))))
    simp [symmDiff_def]
  · apply Computable.primrec (Primrec.finite (Finite.Set.subset hXY.toFinset ?_))
    simp [Set.symmDiff_def]

/-- If X=*Y, then X is partial recursive iff Y is -/
theorem partrec_set_eq_star_iff (hXY : X =* Y) : set X ↔ set Y := by
  constructor
  · exact partrec_set_eq_star hXY
  · rw [eq_star_comm] at hXY
    exact partrec_set_eq_star hXY
