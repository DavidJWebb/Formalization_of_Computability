/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David J. Webb
-/

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Basic
import Mathlib.Order.SymmDiff

set_option warningAsError false

/-
Set definitions for primitive/partial recursiveness and computability.
Each such set is the domain of its respective type of function.
This allows for set operations such as union, intersection, set difference, and complement,
and definitions of classical recusion theory notions like immunity and cohesiveness.
-/

def set_primrec (X : Set ℕ) : Prop :=
∃ (f : ℕ → Bool), Primrec f ∧ ∀ x, x ∈ X ↔ f x = true

def set_computable (X : Set ℕ) : Prop :=
∃ (f : ℕ → Bool), Computable f ∧ ∀ x, x ∈ X ↔ f x = true
abbrev Delta01 := set_computable

def set_partrec (X : Set ℕ) : Prop :=
∃ (f: ℕ →. Option Unit), Partrec f ∧ f.Dom = X
abbrev Sigma01 := set_partrec

-- Implications
theorem set_primrec_is_computable (X : Set ℕ) (h : set_primrec X) :
set_computable X := by
obtain ⟨f, ⟨hPrim, hSpec⟩⟩ := h
use f
constructor
· apply Primrec.to_comp
  exact hPrim
· exact hSpec

theorem set_computable_is_partrec (X : Set ℕ) (h : set_computable X) :
set_partrec X := by
  obtain ⟨f, ⟨hComp, hSpec⟩⟩ := h
  let f' : ℕ →. Option Unit := λ x => bif f x then Part.some () else Part.none
  use f'
  constructor
  · apply Partrec.cond hComp
    exact Partrec.const' (Part.some true)
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

theorem set_primrec_is_partrec (X : Set ℕ) (h : set_primrec X) :
set_partrec X := by
apply set_computable_is_partrec
apply set_primrec_is_computable
exact h

-- ℕ
theorem nat_primrec : set_primrec (Set.univ : Set ℕ) := by
use (fun _ => true)
constructor
· apply Primrec.const
· simp

theorem nat_computable : set_computable (Set.univ : Set ℕ) := by
apply set_primrec_is_computable
exact nat_primrec

theorem nat_partrec : set_partrec (Set.univ : Set ℕ) := by
apply set_computable_is_partrec
exact nat_computable

-- The empty set
theorem empty_set_primrec : set_primrec (∅ : Set ℕ) := by
use (fun _ => false)
constructor
· apply Primrec.const
· simp

theorem empty_set_computable : set_computable (∅ : Set ℕ) := by
apply set_primrec_is_computable
exact empty_set_primrec

theorem empty_set_partrec : set_partrec (∅ : Set ℕ) := by
apply set_computable_is_partrec
exact empty_set_computable

-- Singletons
theorem singleton_primrec (a : ℕ) : set_primrec ({a} : Set ℕ) := by
  let f : ℕ → Bool := λ n => bif n = a then true else false
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

theorem singleton_computable (a : ℕ) : set_computable ({a} : Set ℕ) := by
  apply set_primrec_is_computable
  exact singleton_primrec a

theorem singleton_partrec (a : ℕ) : set_partrec ({a} : Set ℕ) := by
  apply set_computable_is_partrec
  exact singleton_computable a

-- Unions
theorem set_primrec_union (X Y : Set ℕ) (hX : set_primrec X) (hY : set_primrec Y) :
set_primrec (X ∪ Y) := by
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

theorem set_computable_union (X Y : Set ℕ) (hX : set_computable X) (hY: set_computable Y) :
set_computable (X ∪ Y) := by
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

theorem set_partrec_union (X Y : Set ℕ) (hX : set_partrec X) (hY : set_partrec Y) :
set_partrec (X ∪ Y) := by
obtain ⟨f, ⟨fPrim, fSpec⟩⟩ := hX
obtain ⟨g, ⟨gPrim, gSpec⟩⟩ := hY
have hfg : ∃ (h : ℕ →. Option Unit), -- merge the witnessing functions for Z and {a}
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

-- Intersections
theorem set_primrec_inter (X Y : Set ℕ) (hX : set_primrec X) (hY : set_primrec Y) :
set_primrec (X ∩ Y) := by
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

theorem set_computable_inter (X Y : Set ℕ) (hX : set_computable X) (hY: set_computable Y) :
set_computable (X ∩ Y) := by
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

theorem set_partrec_inter (X Y : Set ℕ) (hX : set_partrec X) (hY : set_partrec Y) :
set_partrec (X ∩ Y) := by
obtain ⟨f, ⟨fPart, fSpec⟩⟩ := hX
obtain ⟨g, ⟨gPart, gSpec⟩⟩ := hY
let h := λ x => (f x).bind (λ _ => g x)
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

-- Complements
theorem set_primrec_compl (X : Set ℕ) (hX : set_primrec X) : set_primrec Xᶜ := by
obtain ⟨f, ⟨fPrim, fSpec⟩⟩ := hX
let f' := fun x => !(f x)
use f'
constructor
· refine Primrec.cond fPrim ?_ ?_
  · exact Primrec.const false
  · exact Primrec.const true
· intro x
  simp [fSpec, f']

theorem set_computable_compl (X : Set ℕ) (hX : set_computable X) : set_computable Xᶜ := by
obtain ⟨f, ⟨fComp, fSpec⟩⟩ := hX
let f' := fun x => !(f x)
use f'
constructor
· refine Computable.cond fComp ?_ ?_
  · exact Computable.const false
  · exact Computable.const true
· intro x
  simp [fSpec, f']

-- Set differences
theorem set_primrec_sdiff (X Y : Set ℕ) (hX : set_primrec X) (hY : set_primrec Y) :
set_primrec (X \ Y) := by
apply set_primrec_compl at hY
apply set_primrec_inter
· exact hX
· exact hY

theorem set_computable_sdiff (X Y : Set ℕ) (hX : set_computable X) (hY : set_computable Y) :
set_computable (X \ Y) := by
apply set_computable_compl at hY
apply set_computable_inter
· exact hX
· exact hY

theorem set_partrec_sdiff_computable (X Y : Set ℕ) (hX : set_partrec X) (hY : set_computable Y) :
set_partrec (X \ Y) := by
apply set_computable_compl at hY
apply set_partrec_inter
· exact hX
· apply set_computable_is_partrec
  exact hY

-- Finite sets
theorem finite_set_primrec (X : Finset ℕ) : set_primrec X := by
  induction' X using Finset.induction_on' with a S ha hS haS hSPrim
  · simp
    exact empty_set_primrec
  · rw [Finset.coe_insert]
    rw [Set.insert_eq]
    apply set_primrec_union
    · exact singleton_primrec a
    · exact hSPrim

theorem finite_set_computable (X : Finset ℕ) : set_computable X := by
apply set_primrec_is_computable
apply finite_set_primrec

theorem finite_set_partrec (X : Finset ℕ) : set_partrec X := by
apply set_computable_is_partrec
apply finite_set_computable

-- Cofinite sets
theorem cofinite_set_primrec (X : Set ℕ) (hX : Xᶜ.Finite): set_primrec X := by
rw [← compl_compl X]
apply set_primrec_compl
let Yc : Finset ℕ := hX.toFinset
have hYc : ↑Yc = Xᶜ := Set.Finite.coe_toFinset hX
rw [← hYc]
apply finite_set_primrec

theorem cofinite_set_computable (X : Set ℕ) (hX : Xᶜ.Finite): set_computable X := by
apply set_primrec_is_computable
apply cofinite_set_primrec
exact hX

theorem cofinite_set_partrec (X : Set ℕ) (hX : Xᶜ.Finite): set_partrec X := by
apply set_computable_is_partrec
apply cofinite_set_computable
exact hX

infixl:100 " ∆ " => symmDiff

-- Symmetric difference
theorem set_primrec_symmdiff (X Y : Set ℕ) (hX : set_primrec X) (hY : set_primrec Y) :
set_primrec (X ∆ Y) := by
rw [Set.symmDiff_def]
apply set_primrec_union
· apply set_primrec_sdiff
  · exact hX
  · exact hY
· apply set_primrec_sdiff
  · exact hY
  · exact hX

theorem set_computable_symmdiff (X Y : Set ℕ) (hX : set_computable X) (hY : set_computable Y) :
set_computable (X ∆ Y) := by
rw [Set.symmDiff_def]
apply set_computable_union
· apply set_computable_sdiff
  · exact hX
  · exact hY
· apply set_computable_sdiff
  · exact hY
  · exact hX

theorem set_partrec_symmdiff_finite (X Y : Set ℕ) (hX : set_partrec X) (hXY : (X ∆ Y).Finite) :
set_partrec Y := by
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
apply set_partrec_sdiff_computable
· apply set_partrec_union
  · exact hX
  · apply finite_set_partrec FC
· apply finite_set_computable FD
