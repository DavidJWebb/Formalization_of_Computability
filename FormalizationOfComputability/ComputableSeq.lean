/-
Copyright (c) 2026 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.PhiSeq
import Mathlib.Order.Interval.Finset.Nat

namespace Computability

/- Given that S is infinitely often some, produce the index of the next some element, starting at s -/
def seekSomeIndex {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) : ℕ :=
    Nat.find (h s)

/- Finding the next some element of an infinite Stream' is computable. -/
lemma computable_seekSomeIndex {α} [Primcodable α] (S : Stream' (Option α))
  [DecidablePred (fun t ↦ ∃ n, S t = some n)] (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n)
  (hP : ComputablePred fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ ∃ n, S p.2 = some n) :
    Computable fun s ↦ seekSomeIndex S h s := by
  let q : ℕ → ℕ → Bool := fun s t ↦ decide (s ≤ t ∧ ∃ n, S t = some n)
  obtain ⟨x, hq₀⟩ := hP
  refine Partrec.of_eq_tot (Partrec.rfind (hq₀.to₂).partrec₂) ?_
  intro s
  rw [Nat.mem_rfind]
  dsimp [q, seekSomeIndex]
  constructor
  · simp [Nat.find_spec (h s)]
  · intro m hm
    simp [Nat.find_min (h s) hm]

/- Given that S is infinitely often some, produce the next some element, starting at s -/
def seekSome {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) : α :=
    (S (Nat.find (h s))).get
  (by exact Option.isSome_iff_exists.mpr ((Nat.find_spec (h s)).2))

lemma seekSome_spec {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) :
    S (seekSomeIndex S h s) = some (seekSome S h s) := by
  simp only [seekSomeIndex, ge_iff_le, seekSome, Option.some_get]

/- The index found by seekSomeIndex is at or after the input index. -/
lemma seekSomeIndex_gt {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) :
    seekSomeIndex S h s ≥ s := by
  exact (Nat.find_spec (h s)).1

lemma seekSomeIndex_eq_self {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) {s : ℕ} {a : α} (hs : S s = some a) :
    seekSomeIndex S h s = s := by
  apply le_antisymm
  · exact Nat.find_min' (h s) ⟨le_rfl, ⟨a, hs⟩⟩
  · exact seekSomeIndex_gt S h s

-- The index found by seekSomeIndex points to a some value.
lemma seekSomeIndex_isSome {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) :
    ∃ n, S (seekSomeIndex S h s) = some n := by
  exact (Nat.find_spec (h s)).2

/- The indices of the some entries of S. -/
def dropNoneIndex {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) : ℕ → ℕ
    | 0 => seekSomeIndex S h 0
    | s + 1 => seekSomeIndex S h (dropNoneIndex S h s+1)

lemma computable_dropNoneIndex {α} [Primcodable α] (S : Stream' (Option α))
  [DecidablePred (fun t ↦ ∃ n, S t = some n)] (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n)
  (hP : ComputablePred fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ ∃ n, S p.2 = some n) :
    Computable fun s ↦ dropNoneIndex S h s := by
  let seek := seekSomeIndex S h
  have hseek := computable_seekSomeIndex S h hP
  have hrec : Computable fun s : ℕ => Nat.rec (motive := fun _ => ℕ)
      (seek 0) (fun _ IH => seek (IH + 1)) s := by
    let step : ℕ → ℕ × ℕ → ℕ := fun _ p => seek (p.2 + 1)
    have hstep : Computable₂ step := by
      apply Computable₂.mk
      dsimp [step]
      exact hseek.comp <| Computable.succ.comp <| Computable.snd.comp Computable.snd
    simpa [step] using
    (Computable.nat_rec (α := ℕ) (σ := ℕ) (f := fun s : ℕ => s) (g := fun _ : ℕ => seek 0)
      (h := step) Computable.id (Computable.const (seek 0)) hstep)
  refine hrec.of_eq ?_
  intro s
  induction s with
  | zero =>
      rfl
  | succ s ih =>
      simp [dropNoneIndex, seek, ih]

-- The stream obtained from S by deleting all the none entries.
def dropNone {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) : Stream' α :=
    fun s => Option.get (S (dropNoneIndex S h s)) <| by
  apply Option.isSome_iff_exists.mpr
  unfold dropNoneIndex
  cases s with | zero | succ s
  <;> simp [seekSome_spec S h ?_]

/- The value of dropNone at index s agrees with the original stream at index dropNoneIndex S h s. -/
lemma dropNone_spec {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) :
    S (dropNoneIndex S h s) = some (dropNone S h s) := by
  simp only [dropNone, Option.some_get]

lemma computable_dropNone {α} [Primcodable α] (S : Stream' (Option α))
  [DecidablePred (fun t ↦ ∃ n, S t = some n)] (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n)
  (hS : Computable S) (hP : ComputablePred fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ ∃ n, S p.2 = some n) :
    Computable fun s ↦ dropNone S h s := by
  refine Partrec.of_eq_tot (Computable.ofOption (hS.comp (computable_dropNoneIndex S h hP))) ?_
  intro s
  simp only [dropNone_spec, Part.coe_some, Part.mem_some_iff]

/- The indices selected by dropNoneIndex strictly increase. -/
lemma dropNoneIndex_gt {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) :
    dropNoneIndex S h (s + 1) > dropNoneIndex S h s := by
  change seekSomeIndex S h (dropNoneIndex S h s + 1) > dropNoneIndex S h s
  exact seekSomeIndex_gt S h (dropNoneIndex S h s + 1)

/- lemma dropNoneIndex_zero_pos (S : Stream' (Option ℕ)) [DecidablePred (fun t => ∃ n, S t = some n)]
    (h : ∀ N, ∃ t > N, ∃ n, S t = some n) :
    dropNoneIndex S h 0 > 0 := by
  exact seekSomeIndex_gt S h 0 -/

-- The number of some entries occurring strictly before a given index in the stream.
def countSomeBefore {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)] : ℕ → ℕ
  | 0 => 0
  | s + 1 => countSomeBefore S s + if ∃ n, S s = some n then 1 else 0

/- The next some after s in S occurs at the (countSomeBefore S s)th element of dropNone S h. -/
lemma dropNone_countSome {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (s : ℕ) :
    seekSomeIndex S h s = dropNoneIndex S h (countSomeBefore S s) := by
  rw [eq_comm]
  induction s with
  | zero =>
      rfl
  | succ s ih =>
      simp [countSomeBefore]
      by_cases hs : ∃ n, S s = some n
      · obtain ⟨n, hs⟩ := hs
        simp [hs, dropNoneIndex, ih, seekSomeIndex_eq_self S h hs]
      · simp [hs, ih]
        apply Nat.le_antisymm
        · exact Nat.find_min' (h s) ⟨Nat.le_trans (Nat.le_succ s) (seekSomeIndex_gt S h (s + 1)),
            seekSomeIndex_isSome S h (s + 1)⟩
        · refine Nat.find_min' (h (s + 1)) ⟨?_, seekSomeIndex_isSome S h s⟩
          contrapose hs
          have h1 : seekSomeIndex S h s = s := by
            grind only [seekSomeIndex_gt S h s]
          rw [← h1, seekSome_spec S h s]
          simp

lemma dropNone_of_some {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) {s : ℕ} {a : α} (hs : S s = some a) :
    dropNone S h (countSomeBefore S s) = S s := by
  rw [← dropNone_spec S h (countSomeBefore S s), ← dropNone_countSome S h s,
    seekSomeIndex_eq_self S h hs]

/- dropNone S enumerates the same elements as S -/
lemma dropNoneIff {α} (S : Stream' (Option α)) [DecidablePred (fun t => ∃ n, S t = some n)]
  (h : ∀ N, ∃ t ≥ N, ∃ n, S t = some n) (a : α) :
    (∃ s, S s = some a) ↔ (∃ t, dropNone S h t = a) := by
  constructor
  · intro ⟨s, hs⟩
    use countSomeBefore S s
    apply Option.some_inj.mp
    rw [← hs, dropNone_of_some S h hs]
  · intro ⟨t, ht⟩
    refine ⟨dropNoneIndex S h t, ?_⟩
    rw [dropNone_spec S h t, ht]

lemma Wenum_aux (e : ℕ) (h : (W e).Infinite) : ∀ N, ∃ t ≥ N, ∃ n, (Wenum e) t = some n := by
  exact ((We_infinite_TFAE e).out 0 5).mp h

/- If Wenum is known to be infinite, Wenum' collects only the emitted elements -/
def Wenum' (e : ℕ) (h : (W e).Infinite) : Stream' ℕ :=
  dropNone (Wenum e) (Wenum_aux e h)

/- The stage at which the nth element of Wenum is enumerated -/
def enum_stage' (e n : ℕ) (h : (W e).Infinite) : Part ℕ :=
  dropNoneIndex (Wenum e) (Wenum_aux e h) n

/- Wenum' enumerates the same elements as Wenum -/
lemma Wenum'_mem (e n : ℕ) (h : (W e).Infinite) :
    (∃ s, Wenum e s = some n) ↔ (∃ t, Wenum' e h t = n) := by
  unfold Wenum'
  simp_all only [dropNoneIff (Wenum e) (Wenum_aux e h)]

lemma computable_Wenum' (e : ℕ) (h : (W e).Infinite) :
    Computable fun x ↦ Wenum' e h x := by
  change Computable fun x ↦ dropNone (Wenum e) (Wenum_aux e h) x
  apply computable_dropNone
  · sorry
  · have h1 := Wenum_dec e


instance Wenum'_dec (e : ℕ) (h : (W e).Infinite) : ComputablePred fun (n, s) ↦ Wenum' e h s = n := by
  simp
  unfold ComputablePred
  have hP := computable_Wenum' e h



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

/- If W e is infinite and increasing, every emitted element is at least its index -/
lemma inc_ge_index (e : ℕ) (h : (W e).Infinite) (hinc : ∀ m n, m < n → Wenum' e h m < Wenum' e h n) :
    ∀ s, s ≤ Wenum' e h s := by
  intro s
  induction s with | zero | succ s ih
  · exact Nat.zero_le _
  · exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hinc s (s + 1) (Nat.lt_succ_self s)))

lemma inf_inc_sigma01_is_delta01 (e : ℕ) (h : (W e).Infinite)
  (hinc : ∀ m n, m < n → Wenum' e h m < Wenum' e h n) :
    Delta01 (W e) := by
  have hmem (x : ℕ) : x ∈ W e ↔ ∃ n, Wenum' e h n = x := by
    rw [← Wenum'_mem]
    grind [(We_mem_TFAE e x).out 0 3]
  have hx (x : ℕ) : x ∈ W e ↔ (∃ s < x+1, Wenum' e h s = x) := by
    constructor
    <;> intro h1
    · obtain ⟨s, h1⟩ := (hmem x).mp h1
      refine ⟨s, ⟨?_, h1⟩⟩
      have hs := inc_ge_index e h hinc s
      rw [h1] at hs
      exact Nat.lt_succ_of_le hs
    · obtain ⟨s, ⟨_, h2⟩⟩ := h1
      apply (hmem x).mpr
      use s
  refine (Computable.set_iff_ComputablePred (W e)).mpr ?_
  simp_rw [hx, ← Finset.mem_range, ← Finset.mem_toList]
  have hR : ComputablePred fun (n, s) ↦ Wenum' e h s = n := Wenum'_dec e h



-- Views Of Mount Σ01 :
-- partial recursive f
-- its domain X
-- the range of a computable g : ℕ → ℕ
-- the code e for f
-- the (possibly finite) sequence of nth outputs {fn}
-- the infinite partial recursive sequence of nth outputs {fn}

-- #min_imports
