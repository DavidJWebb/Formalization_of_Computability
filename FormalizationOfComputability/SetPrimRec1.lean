/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/

import Mathlib.Computability.Halting
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-
# Sets for Computability Theory
This file provides set definitions for primitive/partial recursiveness and computability.
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
- '∆' is used for symmetric difference (see symmDiff)
-/
namespace Computability

def PrimrecSet (X : Set ℕ) : Prop :=
    ∃ (f : ℕ → Bool), Primrec f ∧ ∀ x, x ∈ X ↔ f x = true
def ComputableSet (X : Set ℕ) : Prop :=
    ∃ (f : ℕ → Bool), Computable f ∧ ∀ x, x ∈ X ↔ f x = true
def PartrecSet (X : Set ℕ) : Prop :=
    ∃ (f: ℕ →. Unit), Partrec f ∧ f.Dom = X

abbrev Delta01 := ComputableSet
abbrev Sigma01 := PartrecSet

-- Implications
theorem PrimrecSet.computable (X : Set ℕ) (h : PrimrecSet X) :
    ComputableSet X := by
  obtain ⟨f, ⟨hPrim, hSpec⟩⟩ := h
  use f
  constructor
  · apply Primrec.to_comp
    exact hPrim
  · exact hSpec
abbrev PrimrecSet.Delta01 := PrimrecSet.computable

theorem ComputableSet.partrec (X : Set ℕ) (h : ComputableSet X) :
    PartrecSet X := by
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
abbrev Delta01.Sigma01 := ComputableSet.partrec

theorem PrimrecSet.partrec (X : Set ℕ) (h : PrimrecSet X) :
    PartrecSet X := by
  apply ComputableSet.partrec
  apply PrimrecSet.computable
  exact h
abbrev PrimrecSet.Sigma01 := PrimrecSet.partrec

-- ℕ
theorem nat_primrec : PrimrecSet (Set.univ : Set ℕ) := by
  use (fun _ => true)
  constructor
  · apply Primrec.const
  · simp

theorem nat_computable : ComputableSet (Set.univ : Set ℕ) := by
  apply PrimrecSet.computable
  exact nat_primrec
abbrev nat_delta01 := nat_computable

theorem nat_partrec : PartrecSet (Set.univ : Set ℕ) := by
  apply ComputableSet.partrec
  exact nat_computable
abbrev nat_sigma01 := nat_partrec

-- The empty set
theorem empty_PrimrecSet : PrimrecSet (∅ : Set ℕ) := by
  use (fun _ => false)
  constructor
  · apply Primrec.const
  · simp

theorem empty_ComputableSet : ComputableSet (∅ : Set ℕ) := by
  apply PrimrecSet.computable
  exact empty_PrimrecSet
abbrev empty_delta01 := empty_ComputableSet

theorem empty_PartrecSet : PartrecSet (∅ : Set ℕ) := by
  apply ComputableSet.partrec
  exact empty_ComputableSet
abbrev empty_sigma01 := empty_PartrecSet

-- Singletons
theorem singleton_primrec (a : ℕ) : PrimrecSet ({a} : Set ℕ) := by
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

theorem singleton_computable (a : ℕ) : ComputableSet ({a} : Set ℕ) := by
  apply PrimrecSet.computable
  exact singleton_primrec a
abbrev singleton_delta01 (a : ℕ) := singleton_computable a

theorem singleton_partrec (a : ℕ) : PartrecSet ({a} : Set ℕ) := by
  apply ComputableSet.partrec
  exact singleton_computable a
abbrev singleton_sigma01 (a : ℕ) := singleton_partrec a

-- Set Operations

-- Union
theorem PrimrecSet.Union (X Y : Set ℕ) (hX : PrimrecSet X) (hY : PrimrecSet Y) :
    PrimrecSet (X ∪ Y) := by
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

theorem ComputableSet.Union (X Y : Set ℕ) (hX : ComputableSet X) (hY : ComputableSet Y) :
    ComputableSet (X ∪ Y) := by
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
abbrev delta01_union := ComputableSet.Union

theorem PartrecSet.Union (X Y : Set ℕ) (hX : PartrecSet X) (hY : PartrecSet Y) :
    PartrecSet (X ∪ Y) := by
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
abbrev sigma01_union := PartrecSet.Union

-- Intersection
theorem PrimrecSet.Inter (X Y : Set ℕ) (hX : PrimrecSet X) (hY : PrimrecSet Y) :
    PrimrecSet (X ∩ Y) := by
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

theorem ComputableSet.Inter (X Y : Set ℕ) (hX : ComputableSet X) (hY : ComputableSet Y) :
    ComputableSet (X ∩ Y) := by
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
abbrev delta01_inter := ComputableSet.Inter

theorem PartrecSet.Inter (X Y : Set ℕ) (hX : PartrecSet X) (hY : PartrecSet Y) :
    PartrecSet (X ∩ Y) := by
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
abbrev sigma01_inter := PartrecSet.Inter

-- Complement
theorem PrimrecSet.Compl (X : Set ℕ) (hX : PrimrecSet X) : PrimrecSet Xᶜ := by
  obtain ⟨f, ⟨fPrim, fSpec⟩⟩ := hX
  let f' := fun x => !(f x)
  use f'
  constructor
  · refine Primrec.cond fPrim ?_ ?_
    · exact Primrec.const false
    · exact Primrec.const true
  · intro x
    simp [fSpec, f']

theorem PrimrecSet.Compl_iff (X : Set ℕ) : PrimrecSet X ↔ PrimrecSet Xᶜ := by
  constructor
  · exact PrimrecSet.Compl X
  · intro h
    rw [← compl_compl X]
    apply PrimrecSet.Compl Xᶜ
    exact h

theorem ComputableSet.Compl (X : Set ℕ) (hX : ComputableSet X) : ComputableSet Xᶜ := by
  obtain ⟨f, ⟨fComp, fSpec⟩⟩ := hX
  use fun x => !(f x)
  constructor
  · refine Computable.cond fComp ?_ ?_
    · exact Computable.const false
    · exact Computable.const true
  · intro x
    simp [fSpec]
abbrev delta01_compl := ComputableSet.Compl

theorem ComputableSet.Compl_iff (X : Set ℕ) : ComputableSet X ↔ ComputableSet Xᶜ := by
  constructor
  · exact ComputableSet.Compl X
  · intro h
    rw [← compl_compl X]
    apply ComputableSet.Compl Xᶜ
    exact h
abbrev delta01_compl_iff := ComputableSet.Compl_iff

-- Set difference
theorem PrimrecSet.Sdiff (X Y : Set ℕ) (hX : PrimrecSet X) (hY : PrimrecSet Y) :
    PrimrecSet (X \ Y) := by
  apply PrimrecSet.Compl at hY
  apply PrimrecSet.Inter
  · exact hX
  · exact hY

theorem ComputableSet.Sdiff (X Y : Set ℕ) (hX : ComputableSet X) (hY : ComputableSet Y) :
    ComputableSet (X \ Y) := by
  apply ComputableSet.Compl at hY
  apply ComputableSet.Inter
  · exact hX
  · exact hY
abbrev delta01_sdiff := ComputableSet.Sdiff

theorem PartrecSet.Sdiff_computable (X Y : Set ℕ) (hX : PartrecSet X) (hY : ComputableSet Y) :
    PartrecSet (X \ Y) := by
  apply ComputableSet.Compl at hY
  apply PartrecSet.Inter
  · exact hX
  · apply ComputableSet.partrec
    exact hY
abbrev sigma01_sdiff_delta01 := PartrecSet.Sdiff_computable

-- Finite sets
theorem finite_PrimrecSet (X : Set ℕ) (h : X.Finite) : PrimrecSet X := by
  obtain ⟨X, rfl⟩ := Set.Finite.exists_finset_coe h
  induction' X using Finset.induction_on' with a S ha hS haS hSPrim
  · simp
    exact empty_PrimrecSet
  · rw [Finset.coe_insert]
    rw [Set.insert_eq]
    apply PrimrecSet.Union
    · exact singleton_primrec a
    · apply hSPrim
      exact Finite.of_fintype ↑↑S

theorem finite_ComputableSet (X : Set ℕ) (h : X.Finite) : ComputableSet X := by
  apply PrimrecSet.computable
  apply finite_PrimrecSet
  exact h
abbrev finite_delta01 := finite_ComputableSet

theorem finite_PartrecSet (X : Set ℕ) (h : X.Finite) : PartrecSet X := by
  apply ComputableSet.partrec
  apply finite_ComputableSet
  exact h
abbrev finite_sigma01 := finite_PartrecSet

-- Cofinite sets
theorem cofinite_PrimrecSet (X : Set ℕ) (hX : Xᶜ.Finite) : PrimrecSet X := by
  obtain ⟨Xc, hXc⟩ := Set.Finite.exists_finset_coe hX
  rw [← compl_compl X]
  apply PrimrecSet.Compl
  let Yc : Finset ℕ := hX.toFinset
  rw [← hXc]
  apply finite_PrimrecSet
  exact Finite.of_fintype ↑↑Xc

theorem cofinite_ComputableSet (X : Set ℕ) (hX : Xᶜ.Finite) : ComputableSet X := by
  apply PrimrecSet.computable
  apply cofinite_PrimrecSet
  exact hX
abbrev cofinite_delta01 := cofinite_ComputableSet

theorem cofinite_PartrecSet (X : Set ℕ) (hX : Xᶜ.Finite) : PartrecSet X := by
  apply ComputableSet.partrec
  apply cofinite_ComputableSet
  exact hX
abbrev cofinite_sigma01 := cofinite_PartrecSet

infixl:100 " ∆ " => symmDiff

-- Symmetric difference
theorem PrimrecSet.Symmdiff (X Y : Set ℕ) (hX : PrimrecSet X) (hY : PrimrecSet Y) :
    PrimrecSet (X ∆ Y) := by
  rw [Set.symmDiff_def]
  apply PrimrecSet.Union
  · apply PrimrecSet.Sdiff
    · exact hX
    · exact hY
  · apply PrimrecSet.Sdiff
    · exact hY
    · exact hX

theorem ComputableSet.Symmdiff (X Y : Set ℕ) (hX : ComputableSet X) (hY : ComputableSet Y) :
    ComputableSet (X ∆ Y) := by
  rw [Set.symmDiff_def]
  apply ComputableSet.Union
  · apply ComputableSet.Sdiff
    · exact hX
    · exact hY
  · apply ComputableSet.Sdiff
    · exact hY
    · exact hX
abbrev delta01_symmdiff := ComputableSet.Symmdiff

def eq_star (X Y : Set ℕ) : Prop := (X∆Y).Finite

infix:50 " =* " => eq_star

lemma eq_star_comm (X Y : Set ℕ) : X =* Y ↔ Y =* X := by
unfold eq_star
rw [symmDiff_comm]

lemma eq_star_trans (X Y Z : Set ℕ) (hXY : X =* Y) (hYZ : Y =* Z) : X =* Z := by
  unfold eq_star
  exact (Set.Finite.symmDiff_congr hXY).mpr hYZ

lemma finite_eq_star (X Y : Set ℕ) (hXY : X =* Y) (hX : X.Finite): Y.Finite := by
  unfold eq_star at hXY
  rw [Set.symmDiff_def, Set.finite_union] at hXY
  obtain ⟨hXY, hYX⟩ := hXY
  have hY : Y = (Y∩X)∪(Y\X) := by rw [Set.inter_union_diff]
  rw [hY]
  rw [Set.finite_union]
  constructor
  · exact Set.Finite.inter_of_right hX Y
  · exact hYX

lemma finite_eq_star_iff (X Y : Set ℕ) (hXY : X =* Y) : X.Finite ↔ Y.Finite := by
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

lemma infinite_eq_star (X Y : Set ℕ) (hXY : X =* Y) (hX : X.Infinite) : Y.Infinite := by
  by_contra hY
  simp at hY
  revert hX
  simp
  apply finite_eq_star Y
  rw [eq_star_comm]
  exact hXY
  exact hY

lemma infinite_eq_star_iff (X Y : Set ℕ) (hXY : X =* Y) : X.Infinite ↔ Y.Infinite := by
  constructor
  · exact fun a ↦ infinite_eq_star X Y hXY a
  · rw [eq_star_comm] at hXY
    exact fun a ↦ infinite_eq_star Y X hXY a

lemma compl_eq_star (X Y : Set ℕ) (hXY : X =* Y) : Xᶜ =* Yᶜ := by
  unfold eq_star
  unfold eq_star at hXY
  revert hXY
  simp

theorem PartrecSet_eq_star (X Y : Set ℕ) (hXY : X =* Y) :
    PartrecSet X → PartrecSet Y := by
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
  apply PartrecSet.Sdiff_computable
  · apply PartrecSet.Union
    · exact hX
    · apply finite_PartrecSet FC
      exact Finite.of_fintype ↑↑FC
  · apply finite_ComputableSet FD
    exact Finite.of_fintype ↑↑FD

theorem PartrecSet_eq_star_iff (X Y : Set ℕ) (hXY : X =* Y) :
    PartrecSet X ↔ PartrecSet Y := by
  constructor
  · exact fun a ↦ PartrecSet_eq_star X Y hXY a
  · rw [eq_star_comm] at hXY
    exact fun a ↦ PartrecSet_eq_star Y X hXY a

abbrev set_sigma01_eq_star_iff := PartrecSet_eq_star_iff

end Computability

-- #min_imports
