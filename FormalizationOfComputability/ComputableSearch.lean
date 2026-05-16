/-
Copyright (c) 2026 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/

import Mathlib.Computability.Halting
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Computability.Primrec.Basic
import Mathlib.Logic.Encodable.Pi

open List
open Denumerable Encodable Function

namespace Computable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

variable {p : α → Prop} [DecidablePred p]

/-- Filtering a list for elements that satisfy a decidable predicate is primitive recursive. -/
theorem listFilter (hf : ComputablePred p) : Computable fun L : List α ↦ List.filter (p ·) L := by
  unfold Computable Partrec
  simp_all
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Computable₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)


namespace ComputablePred

open List Primrec

variable {α β : Type*} {p : α → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- Checking if any element of a list satisfies a decidable predicate is primitive recursive. -/
theorem exists_mem_list : (hf : ComputablePred p) → ComputablePred fun L : List α ↦ ∃ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (.not <| Primrec.eq.comp (list_length.comp <| listFilter hf.ComputablePred) (const 0)) <| by simp

/-- Checking if every element of a list satisfies a decidable predicate is primitive recursive. -/
theorem forall_mem_list : (hf : ComputablePred p) → ComputablePred fun L : List α ↦ ∀ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (Primrec.eq.comp (list_length.comp <| listFilter hf.ComputablePred) (list_length)) <| by simp

variable {p : ℕ → Prop}

/-- Bounded existential quantifiers are primitive recursive. -/
theorem exists_lt (hf : ComputablePred p) : ComputablePred fun n ↦ ∃ x < n, p x :=
  of_eq (hf.exists_mem_list.comp list_range) (by simp)

/-- Bounded universal quantifiers are primitive recursive. -/
theorem forall_lt (hf : ComputablePred p) : ComputablePred fun n ↦ ∀ x < n, p x :=
  of_eq (hf.forall_mem_list.comp list_range) (by simp)

/-- A helper lemma for proofs about bounded quantifiers on decidable relations. -/
theorem listFilter_listRange {R : ℕ → ℕ → Prop} (s : ℕ) [DecidableRel R] (hf : PrimrecRel R) :
    Primrec fun n ↦ (range s).filter (fun y ↦ R y n) := by
  simp only [← filterMap_eq_filter]
  refine listFilterMap (.const (range s)) ?_
  refine ite (Primrec.eq.comp ?_ (const true)) (option_some_iff.mpr snd) (.const Option.none)
  exact hf.decide.comp snd fst

end ComputablePred

namespace PrimrecRel

open Primrec List ComputablePred

variable {α β : Type*} {R : α → β → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, it is primitive recursive
to filter `L` for elements `a` with `R a b` -/
theorem listFilter (hf : PrimrecRel R) [DecidableRel R] :
    Primrec₂ fun (L : List α) b ↦ L.filter (fun a ↦ R a b) := by
  simp only [← List.filterMap_eq_filter]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact Primrec.eq.comp (hf.decide.comp snd (snd.comp fst)) (.const true)
  · exact (option_some).comp snd

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∃ a L, R a b`
is a primitive recursive relation. -/
theorem exists_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∃ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length ≠ 0 ↔ ∃ a ∈ L, R a b := by simp
  refine .of_eq (.not ?_) h
  exact Primrec.eq.comp (list_length.comp hf.listFilter) (const 0)

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∀ a L, R a b`
is a primitive recursive relation. -/
theorem forall_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∀ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length = L.length ↔ ∀ a ∈ L, R a b := by simp
  apply PrimrecRel.of_eq ?_ h
  exact (Primrec.eq.comp (list_length.comp <| PrimrecRel.listFilter hf) (.comp list_length fst))

variable {R : ℕ → ℕ → Prop}

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∃ x < n, R x y` is a
primitive recursive relation. -/
theorem exists_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (hf.exists_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∀ x < n, R x y` is a
primitive recursive relation. -/
theorem forall_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (hf.forall_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

end PrimrecRel
