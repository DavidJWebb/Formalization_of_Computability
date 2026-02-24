/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.PhiSeq
import Mathlib.Data.List.TFAE
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Stream.Defs

namespace Computability

-- the first Some element of a stream
def seekSome (S : Stream' (Option ℕ)) [DecidablePred (fun k => ∃ n, S k = some n)]
  (h : ∃ k n, S k = some n) : Stream' (Option ℕ) :=
  Stream'.drop (Nat.find h) S

-- dropping the first k elements of a stream (starting at zero) makes the stream start
-- with the kth element
lemma head_drop (S : Stream' (Option ℕ)) (k : ℕ) :
  (Stream'.drop k S).head = S k := by
  revert S
  induction k with | zero | succ k ih
  · intro S
    exact (Option.map_inj_right fun x y a ↦ a).mp rfl
  · intro S
    simp only [Stream'.head, Stream'.get, Stream'.drop, zero_add]

-- properties of seekSome
lemma seekSome_spec (S : Stream' (Option ℕ)) [DecidablePred (fun k => ∃ n, S k = some n)]
    (h : ∃ k n, S k = some n) :
    ∃ k, seekSome S h = Stream'.drop k S ∧ (seekSome S h).head = S k := by
  refine ⟨Nat.find h, rfl, ?_⟩
  simp only [seekSome, head_drop]

-- delete blank spaces in a stream that is known to be infinite
def dropNone (S : Stream' (Option ℕ))
  [dec : DecidablePred (fun k => ∃ n, S k = some n)]
  (h : ∀ N, ∃ n > N, ∃ k, S n = some k) : Stream' ℕ :=
  let h0 : ∃ k n, S k = some n :=
    let ⟨n, _, k, hk⟩ := h 0
    ⟨n, k, hk⟩   -- note we swap n/k to match seekSome type
  let S' := seekSome S h0
  Stream'.corec
    (fun s => s.head.getD 0)
    (fun s => s.tail)
    S'

-- TODO: prove DecidablePred (fun k => ∃ n, Wenum e k = some n)
-- so that this doesn't need that hypothesis

-- flatten known infinite Wenum streams
def Wenum' (e : ℕ)
  (dec : DecidablePred (fun k => ∃ n, Wenum e k = some n))
  (h: (W e).Infinite)
  : Stream' ℕ :=
  dropNone (Wenum e) (by
    have h1 := ((We_infinite_TFAE e).out 0 5).mp h
    simp_all only [W, gt_iff_lt, ne_eq, Option.ne_none_iff_exists', implies_true]
    )

-- TODO: rephrase for general infinte streams
def enum_stage' (e n : ℕ) (dec : DecidablePred (fun k => ∃ n, Wenum e k = some n))
  (h: (W e).Infinite): Part ℕ :=
  Nat.rfind (fun s => (Wenum' e dec h s == some n))

-- TODO: rephrease for general infinite streams
lemma enum_convert (e n : ℕ) (S : Stream' (Option ℕ)) :
    (∃ s, n = dropNone S s) ↔ (∃ t, some n = S t) := by
  sorry

lemma enum_stage'_exists (e n : ℕ) (h : n ∈ W e) : (enum_stage' e n).Dom := by
  sorry


def Pi01 (X : Set ℕ): Prop := Sigma01 Xᶜ

theorem delta01_is_sigma01 (X : Set ℕ) (h: Delta01 X) : Sigma01 X := Partrec.computable h

theorem delta01_is_pi01 (X : Set ℕ) (h: Delta01 X) : Pi01 X :=
  Partrec.computable (Computable.compl h)

theorem delta01_iff_sigma01_and_pi01 (X : Set ℕ) : Delta01 X ↔ Sigma01 X ∧ Pi01 X := by
  constructor
  · intro h
    constructor
    · apply delta01_is_sigma01
      exact h
    · apply delta01_is_pi01
      exact h
  · intro h
    unfold Pi01 Sigma01 at h
    unfold Delta01
    rw [Computable.set_iff_ComputablePred, ComputablePred.computable_iff_re_compl_re']
    simp_all [Partrec.set_iff_REPred]

lemma inf_inc_sigma01_seq_is_delta01 (e : ℕ) (h1 : (W e).Infinite)
    (h2 : ∀ (n : ℕ), Wenum' e n < Wenum' e (n+1)) : Delta01 (W e) := by

  -- Step 1: membership characterized by enumeration
  have hmem :
    ∀ x, x ∈ W e ↔ ∃ n, Wenum' e n = x := by sorry
  -- Step 2: show bounded search
  have hbound (x : ℕ) (hx : x ∈ W e):
    ∃ N, ∀ n ≥ N, x < Wenum' e n := by
    apply (hmem x).mp at hx
    obtain ⟨N, hx⟩ := hx
    use N+1
    intro n h
    rw [← hx]
    induction n with | zero | succ n ih
    · sorry
    · by_cases h3 : n≥N+1
      · apply ih at h3
        apply lt_trans h3 (h2 n)
      · simp at h
        simp at h3
        have h4 : n = N := by exact Nat.eq_of_le_of_lt_succ h h3
        rw [h4]
        apply h2 N








  -- Step 3: derive decidability
  have hdec : DecidablePred (fun x => x ∈ W e) := by sorry
  -- prove equivalence using monotonicity





-- for any given x, ∃ n x < W_enum n (lest W e not be increasing and infinite)
-- if ∃ m < n x = W_enum m, then x ∈ W e
-- else x ∉ W e
-- bounded quantifiers are decidable

-- Views Of Mount Σ01 :
-- partial recursive f
-- its domain X
-- the range of a computable g : ℕ → ℕ
-- the code e for f
-- the (possibly finite) sequence of nth outputs {fn}
-- the infinite partial recursive sequence of nth outputs {fn}
