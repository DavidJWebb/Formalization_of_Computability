import Mathlib.Computability.Primrec

open List
open Nat
open Primrec

namespace Primrec

/- Filtering a list for elements that meet a decidable condition is primitive recursive -/
lemma filter {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
(hf : PrimrecPred f) : Primrec λ L => (filter (fun a => f a) L) := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap
  · exact Primrec.id
  · simp [Primrec₂, Option.guard]
    apply ite
    · apply PrimrecPred.comp hf snd
    · apply option_some_iff.mpr snd
    · apply const none

/- Checking if any element of a list satisfies a decidable condition is primitive recursive -/
lemma filter_exists {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
    (hf : PrimrecPred f) : PrimrecPred λ (L : List α) => (∃ a ∈ L, f a) := by
  let g := λ L => List.filter (λ a => f a) L
  have h (L : List α): ((g L).length ≠ 0) ↔ (∃ a ∈ L, f a) := by
    simp [g]
  have h1 : PrimrecPred (λ L => (g L).length ≠ 0) := by
    apply PrimrecPred.not
    apply PrimrecRel.comp Primrec.eq ?_ (const 0)
    apply comp list_length (filter f hf)
  exact PrimrecPred.of_eq h1 h

/- Checking if every element of a list satisfies a decidable condition is primitive recursive -/
lemma filter_forall {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
    (hf : PrimrecPred f) : PrimrecPred λ (L : List α) => (∀ a ∈ L, f a) := by
  let g := λ L => List.filter (λ a => f a) L
  have h (L : List α): ((g L).length = L.length) ↔ (∀ a ∈ L, f a) := by
    simp [g]
  have h1 : PrimrecPred (λ L => ((g L).length = L.length)) := by
    refine PrimrecRel.comp Primrec.eq ?_ list_length
    refine comp list_length ?_
    apply filter
    exact hf
  exact PrimrecPred.of_eq h1 h

/- Bounded existential quantifiers are primitive recursive -/
lemma bounded_exists (f : ℕ → Prop) [DecidablePred f] (hf : PrimrecPred f) :
    PrimrecPred λ n => ∃ x < n, f x := by
  have h : PrimrecPred λ n => (∃ a ∈ (range n), f a) := by
    apply PrimrecPred.comp (filter_exists f hf) list_range
  apply PrimrecPred.of_eq h
  simp

/- Bounded universal quantifiers are primitive recursive -/
lemma bounded_forall (f : ℕ → Prop) [DecidablePred f] (hf1 : PrimrecPred f) :
    PrimrecPred λ n => ∀ x < n, f x := by
  have h : (λ n => decide (∀ x < n, f x)) =
            (λ n => decide ((range n).filter (fun x => f x) = range n)) := by simp
  simp [PrimrecPred, h]
  · apply PrimrecRel.comp
    · exact Primrec.eq
    · exact comp (filter f hf1) (list_range)
    · exact list_range

end Primrec

namespace primrec₂

/- The original version, just for ℕ -/
/- lemma filter0 (f : ℕ → ℕ → Prop) (s : ℕ) [∀ y, DecidablePred (f y)] (hf : PrimrecRel f) :
    Primrec λ n => ((range (s)).filter (fun y => f y n)) := by
  let g (n : ℕ): ℕ → Option Nat := (λ y => (if f y n = True then y else Option.none))
  have h (n : ℕ): (range (s)).filter (fun y => f y n) = filterMap (g n) (range s) := by
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
    · exact Primrec.const Option.none -/

/- If f a b is decidable, then given L : List α and b : β, it is primitive recurisve
to filter L for elements a with f a b -/
lemma filter {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [∀ y, DecidablePred (f y)] (hf : PrimrecRel f) :
    Primrec₂ λ b => (λ (L : List α) => (L.filter (fun a => f a b))) := by
  let g (b : β) : α → Option α := (λ a => (if f a b = True then a else Option.none))
  have h (b : β) (L : List α): L.filter (fun a => f a b) = filterMap (g b) L := by
    simp [g]
    symm
    apply filtermap_filter
  simp [h]
  apply listFilterMap
  · exact snd
  · apply Primrec.ite
    · simp
      apply PrimrecRel.comp hf snd (Primrec.comp fst fst)
    · exact option_some_iff.mpr snd
    · exact Primrec.const Option.none

lemma filter_exists {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [∀ y, DecidablePred (f y)] (hf : PrimrecRel f) :
    PrimrecRel λ b => λ (L : List α) => decide (∃ a ∈ L, f a b) := by
  have h := filter f hf

  simp
  have h1 (b : β) (L : List α): Decidable (List.filter (fun x ↦ decide (f x b)) L ≠ []) := by
    simp
    exact decidableBEx (fun x ↦ f x b) L
  have h2 : (fun (b : β) (L : List α) ↦ ∃ a ∈ L, f a b) =
            (fun (b : β) (L : List α) => decide ((List.filter (fun x => f x b) L) ≠ []) = true) := by
    simp
  simp [h2]
  unfold PrimrecRel







/- If f x y is decidable, then a fixed y, it is primitive recursive
to check whether, for some n, there are any x < n with f x y -/
lemma bounded_exists (f : ℕ → ℕ → Prop) [∀ y, DecidablePred (f y)]
    (hf : PrimrecRel f) : PrimrecRel (λ y => (λ n => (∃ x < n, f x y))) := by
  have h : (λ y => (λ n => (∃ x < n, f x y))) =
            (λ y => (λ n => ((List.range n).filter (fun x => f x y) ≠ []))) := by simp
  have h1 := filter f hf

  apply PrimrecRel.comp₂ (λ b => (λ L => (L.filter (fun a => f a b))))

  have h2 : Primrec₂ fun b n ↦ List.filter (fun a ↦ decide (f a b)) (range n) := by
    apply Primrec₂.swap
    apply Primrec.comp₂

/-
{α : the second input y to f} {β : the bound n on the search}
{γ : Type u_3} {δ : Type u_4}
{R : γ → δ → Prop}
[(a : γ) → (b : δ) → Decidable (R a b)]
{f : α → β → γ} {g : α → β → δ}
PrimrecRel R
Primrec₂ f
Primrec₂ g

R0 : ℕ → List ℕ → Prop



(b, L) => (L.filter (fun a => f a b))

R : ∃ x < n, f x y

Conclude PrimrecRel fun (y : α) (n : β) => R (f a b) (g a b)
PrimrecRel fun y n ↦ ∃ x < n, f x y

-/





  simp [PrimrecPred, h]
  apply PrimrecPred.not
  exact PrimrecRel.comp Primrec.eq h1 (Primrec.const [])

/- If f x y is decidable, then given a bound n and a fixed y, it is primitive recursive
to check whether for all x < n, f x y -/
lemma bounded_forall (f : ℕ → ℕ → Prop) (y : ℕ) [∀ y, DecidablePred (f y)]
    (hf : PrimrecRel f) : PrimrecPred λ n => (∀ x < n, (f x y)) := by
  have h : (λ n => decide (∀ x < n, f x y)) =
           (λ n => decide ((range n).filter (fun x => f x y) = range n)) := by simp
  have h1 : Primrec λ n => ((range (n)).filter (fun x => f x y)) := by
    refine Primrec.comp ?_ ?_
    · apply Primrec.filter (fun x ↦ f x y)
      exact PrimrecRel.comp hf Primrec.id (Primrec.const y)
    · exact list_range
  simp [PrimrecPred, h]
  exact PrimrecRel.comp Primrec.eq h1 list_range

end primrec₂
