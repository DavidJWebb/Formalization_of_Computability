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
partial def seekSome (S : Stream' (Option ℕ)) : Stream' (Option ℕ) :=
  match S.head with
  | some _ => S
  | none   => seekSome S.tail

-- delete blank spaces in a stream
def dropNone (s : Stream' (Option ℕ)) : Stream' ℕ :=
  Stream'.corec
    (fun s => match (seekSome s).head with
      | some n => n
      | none   => 0  ) -- if the Stream' is infinite, this is never reached
    (fun s => (seekSome s).tail) s

def Wenum' (e : ℕ) : Stream' ℕ :=
  dropNone (Wenum e)


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
    sorry
  -- given x, create the set of Wenum


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
