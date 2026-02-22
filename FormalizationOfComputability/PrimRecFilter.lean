/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import Mathlib.Computability.Primrec.List
/-

# Bounded quantifiers are primitive recursive
This file contains lemmata for showing bounded existentially and universally quantified
statements are primitive recursive, as well as more general filtering for arbitrary
primcodable types.

## Main results
- Filtering for elements from a list that meet a primrec criterion is primrec
- Checking whether a list has some element meeting a primrec criterion is primrec
- Checking whether every element of a list meets a primrec criterion is primrec
- Primitive recursive functions are closed under bounded existential and universal quantifiers

## References
- [R. I. Soare *Turing Computability - Theory and Applications*] [Soare2016]
-/

open List
open Primrec

namespace Primrec

/- Filtering a list for elements that satisfy a decidable predicate is primitive recursive -/
lemma list_filter {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
(hf : PrimrecPred f) : Primrec λ L => (filter (fun a => f a) L) := by
  exact listFilter hf

/- Checking if any element of a list satisfies a decidable predicate is primitive recursive -/
lemma filter_exists {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
    (hf : PrimrecPred f) : PrimrecPred λ (L : List α) => (∃ a ∈ L, f a) := by
  exact PrimrecPred.exists_mem_list hf

/- Checking if every element of a list satisfies a decidable predicate is primitive recursive -/
lemma filter_forall {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
    (hf : PrimrecPred f) : PrimrecPred λ (L : List α) => (∀ a ∈ L, f a) := by
  exact PrimrecPred.forall_mem_list hf

/- Bounded existential quantifiers are primitive recursive -/
lemma bounded_exists (f : ℕ → Prop) [DecidablePred f] (hf : PrimrecPred f) :
    PrimrecPred λ n => ∃ x < n, f x := by
  exact PrimrecPred.exists_lt hf

/- Bounded universal quantifiers are primitive recursive -/
lemma bounded_forall (f : ℕ → Prop) [DecidablePred f] (hf : PrimrecPred f) :
    PrimrecPred λ n => ∀ x < n, f x := by
  exact PrimrecPred.forall_lt hf

end Primrec

namespace primrec₂

/- If f a b is decidable, then given L : List α and b : β, it is primitive recurisve
to filter L for elements a with f a b -/
lemma list_filter {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [DecidableRel f] (hf : PrimrecRel f) :
    Primrec₂ λ (L : List α) => λ b => (L.filter (fun a => f a b)) := by
  exact PrimrecRel.listFilter hf

end primrec₂

namespace PrimrecRel

lemma filter_exists {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [DecidableRel f] (hf : PrimrecRel f) :
    PrimrecRel λ (L : List α) => λ b => (∃ a ∈ L, f a b) := by
  exact exists_mem_list hf

lemma filter_forall {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [DecidableRel f] (hf : PrimrecRel f) :
    PrimrecRel λ (L : List α) => λ b => (∀ a ∈ L, f a b) := by
  exact forall_mem_list hf

/- Bounded existential quantifiers are primitive recursive -/
lemma bounded_exists (f : ℕ → ℕ → Prop) [DecidableRel f]
    (hf : PrimrecRel f) : PrimrecRel (λ n => (λ y => (∃ x < n, f x y))) := by
  exact exists_lt hf

/- Bounded universal quantifiers are primitive recursive -/
lemma bounded_forall (f : ℕ → ℕ → Prop) [DecidableRel f]
    (hf : PrimrecRel f) : PrimrecRel (λ n => (λ y => (∀ x < n, f x y))) := by
  exact forall_lt hf

end PrimrecRel

namespace Primrec

lemma rel_list_filter (f : ℕ → ℕ → Prop) (s : ℕ) [∀ y, DecidablePred (f y)] (hf : PrimrecRel f) :
    Primrec λ n => ((List.range (s)).filter (fun y => f y n)) := by
  exact PrimrecPred.listFilter_listRange s hf

end Primrec

namespace PrimrecPred

lemma bounded_exists (f : ℕ → ℕ → Prop) (s : ℕ) [DecidableRel f]
    (hf : PrimrecRel f) :
    PrimrecPred (λ n => ∃ y < s, (f y n)) := by
  have h1 : (λ n => decide (∃ y < s, f y n)) =
            (λ n => decide ((List.range s).filter (fun y => f y n) ≠ [])) := by simp
  simp [PrimrecPred]
  apply PrimrecPred.not
  apply PrimrecRel.comp Primrec.eq ?_ (const [])
  apply rel_list_filter
  exact hf

lemma bounded_forall (f : ℕ → ℕ → Prop) (s : ℕ) [∀ y, DecidablePred (f y)]
    (hf : PrimrecRel f) :
    PrimrecPred (λ n => ∀ y < s, (f y n)) := by
  have h1 : (λ n => decide (∀ y < s, f y n)) =
            (λ n => decide ((List.range s).filter (fun y => f y n) = List.range s)) := by simp
  simp [PrimrecPred]
  apply PrimrecRel.comp Primrec.eq
  · apply rel_list_filter
    exact hf
  · exact Primrec.const (range s)

end PrimrecPred
