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

-- the next Some element of a stream
def seekSomeIndex {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) (s : ℕ) : ℕ :=
  Nat.find (h s)

-- the next Some element occurs later
lemma seekSomeIndex_gt {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) (s : ℕ) :
    seekSomeIndex S h s > s := by
  exact (Nat.find_spec (h s)).1

-- the next Some element occurs
lemma seekSomeIndex_isSome {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) (s : ℕ) :
    ∃ n, S (seekSomeIndex S h s) = some n := by
  exact (Nat.find_spec (h s)).2

-- redinexing a known infinite stream to have no nones
def dropNoneIndex {α} (S : Stream' (Option α))
    [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) : ℕ → ℕ
  | 0 => seekSomeIndex S h 0
  | s + 1 => seekSomeIndex S h (dropNoneIndex S h s)

-- the result of this reindexing is only somes
lemma dropNoneIndex_isSome {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) (s : ℕ) :
    ∃ n, S (dropNoneIndex S h s) = some n := by
  cases s with
  | zero =>
      exact seekSomeIndex_isSome S h 0
  | succ s =>
      change ∃ n, S (seekSomeIndex S h (dropNoneIndex S h s)) = some n
      exact seekSomeIndex_isSome S h (dropNoneIndex S h s)

-- the reindexed stream
def dropNone (S : Stream' (Option ℕ)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) : Stream' ℕ :=
  fun s => Nat.find (dropNoneIndex_isSome S h s)

lemma dropNone_spec (S : Stream' (Option ℕ)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) (s : ℕ) :
    S (dropNoneIndex S h s) = some (dropNone S h s) := by
  exact Nat.find_spec (dropNoneIndex_isSome S h s)

/- lemma dropNoneIndex_zero_pos (S : Stream' (Option ℕ)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) :
    dropNoneIndex S h 0 > 0 := by
  exact seekSomeIndex_gt S h 0 -/

lemma dropNoneIndex_step_gt (S : Stream' (Option ℕ)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) (s : ℕ) :
    dropNoneIndex S h (s + 1) > dropNoneIndex S h s := by
  change seekSomeIndex S h (dropNoneIndex S h s) > dropNoneIndex S h s
  exact seekSomeIndex_gt S h (dropNoneIndex S h s)

lemma Wenum_aux (e : ℕ) (h: (W e).Infinite) : ∀ N, ∃ t > N, ∃ n, (Wenum e) t = some n := by
  have h1 := ((We_infinite_TFAE e).out 0 5).mp h
  simp_all only [W, gt_iff_lt, ne_eq, Option.ne_none_iff_exists', implies_true]

/- If Wenum is known to be infinite, Wenum' collects only the emitted elements -/
def Wenum' (e : ℕ) (h: (W e).Infinite) : Stream' ℕ :=
  dropNone (Wenum e) (Wenum_aux e h)

def enum_stage' (e n : ℕ) (h : (W e).Infinite) : Part ℕ :=
  dropNoneIndex (Wenum e) (Wenum_aux e h) n

def Pi01 (X : Set ℕ): Prop := Sigma01 Xᶜ

theorem delta01_is_sigma01 (X : Set ℕ) (h: Delta01 X) : Sigma01 X := Partrec.computable h

theorem delta01_is_pi01 (X : Set ℕ) (h: Delta01 X) : Pi01 X := Partrec.computable (Computable.compl h)

theorem delta01_iff_sigma01_and_pi01 (X : Set ℕ) : Delta01 X ↔ Sigma01 X ∧ Pi01 X := by
  constructor
  · intro h
    exact ⟨delta01_is_sigma01 X h, delta01_is_pi01 X h⟩
  · intro h
    unfold Pi01 Sigma01 at h
    unfold Delta01
    rw [Computable.set_iff_ComputablePred, ComputablePred.computable_iff_re_compl_re']
    simp_all [Partrec.set_iff_REPred]

lemma inf_inc_sigma01_is_delta01 (e : ℕ) (h1 : (W e).Infinite)
    (h2 : ∀ (n : ℕ), (Wenum' e h1 n) < (Wenum' e h1 (n+1))) : Delta01 (W e) := by

  -- Step 1: membership characterized by enumeration
  have hmem :
    ∀ x, x ∈ W e ↔ ∃ n, Wenum' e h1 n = x := by sorry
  -- Step 2: show bounded search
  have hbound (x : ℕ) (hx : x ∈ W e):
    ∃ N, ∀ n ≥ N, x < Wenum' e h1 n := by
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
  have hdec : DecidablePred (fun x => x ∈ W e) := by
    sorry
  -- prove equivalence using monotonicity
  sorry




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
