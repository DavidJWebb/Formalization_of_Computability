import Mathlib.Computability.Primrec

namespace Computability

open List
open Nat
open Primrec

lemma filtermap_filter (A : ℕ → Prop) (n : ℕ) (hf : DecidablePred A) :
    filterMap (fun y => if A y then some y else none) (range n) =
    filter (fun y => decide (A y)) (range n) := by
  induction' n with n ih
  · simp
  · simp [range_succ]
    by_cases h : A n
    · simp [h]
      exact ih
    · simp [h]
      exact ih

lemma primrec_filter (f : ℕ → Prop) [DecidablePred f] (hf1 : PrimrecPred f) :
    Primrec λ n => ((List.range (n)).filter (fun y => f y)) := by
  let g : ℕ → Option Nat := (λ y => (if f y = True then y else Option.none))
  have h (n : ℕ): (range (n)).filter (fun y => f y) = filterMap g (List.range n) := by
    simp [g]
    symm
    apply filtermap_filter
  simp [h]
  apply listFilterMap
  · exact list_range
  · apply Primrec.ite
    · simp
      refine PrimrecPred.comp hf1 ?_
      exact snd
    · refine option_some_iff.mpr ?_
      exact snd
    · exact Primrec.const Option.none

lemma primrec_bounded_exist (f : ℕ → Prop) [DecidablePred f] (hf1 : PrimrecPred f) :
    PrimrecPred λ n => ∃ x < n, f x := by
  have h1 : (λ n => decide (∃ x < n, f x)) =
            (λ n => decide ((List.range (n)).filter (fun x => f x)≠[])) := by simp
  simp [PrimrecPred, h1]
  apply PrimrecPred.not
  apply PrimrecRel.comp
  · exact Primrec.eq
  · exact primrec_filter f hf1
  · exact Primrec.const []

lemma primrec_bounded_forall (f : ℕ → Prop) [DecidablePred f] (hf1 : PrimrecPred f) :
    PrimrecPred λ n => ∀ x < n, f x := by
  have h1 : (λ n => decide (∀ x < n, f x)) =
            (λ n => decide ((List.range n).filter (fun x => f x) = List.range n)) := by simp
  simp [PrimrecPred, h1]
  · apply PrimrecRel.comp
    · exact Primrec.eq
    · exact primrec_filter f hf1
    · exact list_range

lemma primrec_filter₂ (f : ℕ → ℕ → Prop) (s : ℕ) [∀ y, DecidablePred (f y)] (hf : PrimrecRel f) :
    Primrec λ n => ((List.range (s)).filter (fun y => f y n)) := by
  let g (n : ℕ): ℕ → Option Nat := (λ y => (if f y n = True then y else Option.none))
  have h (n : ℕ): (range (s)).filter (fun y => f y n) = filterMap (g n) (List.range s) := by
    simp [g]
    symm
    apply filtermap_filter
  simp [h]
  apply listFilterMap
  · exact Primrec.const (range s)
  · apply Primrec.ite
    · simp
      exact PrimrecRel.comp hf snd fst
    · exact option_some_iff.mpr snd
    · exact Primrec.const Option.none

lemma primrec_bounded_exist₂ (f : ℕ → ℕ → Prop) (s : ℕ) [∀ y, DecidablePred (f y)]
    (hf : PrimrecRel f) :
    PrimrecPred (λ n => ∃ y < s, (f y n)) := by
  have h1 : (λ n => decide (∃ y < s, f y n)) =
            (λ n => decide ((List.range s).filter (fun y => f y n) ≠ [])) := by simp
  simp [PrimrecPred, h1]
  apply PrimrecPred.not
  apply PrimrecRel.comp Primrec.eq
  · apply primrec_filter₂
    exact hf
  · exact Primrec.const []

lemma primrec_bounded_forall₂ (f : ℕ → ℕ → Prop) (s : ℕ) [∀ y, DecidablePred (f y)]
    (hf : PrimrecRel f) :
    PrimrecPred (λ n => ∀ y < s, (f y n)) := by
  have h1 : (λ n => decide (∀ y < s, f y n)) =
            (λ n => decide ((List.range s).filter (fun y => f y n) = List.range s)) := by simp
  simp [PrimrecPred, h1]
  apply PrimrecRel.comp Primrec.eq
  · apply primrec_filter₂
    exact hf
  · exact Primrec.const (range s)
