/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.SetPrimRec
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Linarith

set_option warningAsError false

namespace Nat.Partrec

/- ϕₑ,ₛ(_) -/
def Phi_stage (e s : ℕ) : ℕ → Option ℕ :=
    Code.evaln s (Code.ofNatCode e)

/- ϕₑ(_) -/
def Phi (e : ℕ) : ℕ →. ℕ :=
    (Code.ofNatCode e).eval

/- halting -/
def Phi_stage_halts (e s n : ℕ) : Prop :=
    ∃ (x : ℕ), x ∈ Phi_stage e s n
def Phi_halts (e n : ℕ) : Prop :=
    ∃ (x : ℕ), x ∈ Phi e n
def Phi_stage_diverges (e s n : ℕ) : Prop :=
    ¬ Phi_stage_halts e s n
def Phi_diverges (e n : ℕ) : Prop :=
    ¬ Phi_halts e n

theorem phi_halts_use (e n : ℕ) :
    Phi_halts e n ↔ ∃ (s : ℕ), Phi_stage_halts e s n := by
sorry

/- Wₑ,ₛ = {n | n ≤ s ∧ ϕₑ,ₛ(n)↓} -/
def Weg_stage (e s : ℕ) : Finset ℕ :=
    (Finset.range (s)).filter (λ n => (Phi_stage e s n).isSome)

/- Wₑ = {n | n ≤ s ∧ ϕₑ(n)↓} -/
def Weg (e : ℕ) : Set ℕ := {n | (Phi e n).Dom}

/- Weg e s \ Weg e (s-1)-/
def Weg_dr (e s : ℕ) : List ℕ :=
  List.range (s + 1) |>
    List.filter (λ n => (Phi_stage e s n).isSome ∧
                         (s = 0 ∨ (Phi_stage e (s - 1) n).isNone))

theorem halt_implies_use_gt_input (e s x n : ℕ) (h : x ∈ (Phi_stage e s n)): n < s := by
  unfold Phi_stage at h
  apply Code.evaln_bound
  exact h



/-
s < t → ϕ_{e,s}(n)↓ → ϕ_{e,t}(n)↓
ϕ_{e,s}(n)↓ → ϕ_{e}(n)↓
ϕ_{e}(n)↓ ↔ ∃ (s : ℕ), ϕ_{e,s}(n)↓


-/


open Nat Part

partial def enumerated_code (e k n : ℕ) : Code := do
  -- concatenate all new_elements_list_code e s for s in [0..n]
  let rec loop (s : ℕ) (acc : List ℕ) : Code := do
    if s > n then
      pure acc
    else do
      let elems ← new_elements_list_code e s 0
      loop (s + 1) (acc ++ elems)
  let enumerated ← loop 0 []
  if k < enumerated.length then
    pure (enumerated.get ⟨k, sorry_proof⟩) -- proof omitted for now
  else
    failure

def Weg_enum (e : ℕ) : ℕ →. ℕ :=
  λ k => Code.rfind' (enumerated_code e k) 0



-- Views Of Mount Σ01 :
-- partial recursive f
-- its domain X
-- the range of a computable g : ℕ → ℕ
-- the code e for f
-- the (possibly finite) sequence of nth outputs {fn}
-- the infinite partial recursive sequence of nth outputs {fn}


-- lemma : an increasing Sigma01 sequence is Delta01-+-

/-
Now we can build W_{e,s} in the order things are enumerated!

s0 = μ t W_{e,t} ≠ ∅           (the least stage when an element is enumerated into W_{e,t})
n0 = μ x evaln x e s0 = 1      (the least element of W_{e,s0})
s (n) = μ t W_{e,t} ≠ {s0, ..., s(n-1)} (the least stage when something new enters W_e)

Note the above handles the case that multiple elements enter at the same stage - W_{e,t}
will not equal the full set until every new element has been included

i n = μ s(n) ∀ (m : ℕ), (m < n) → s(m) < s(n)
That is, the i n are an increasing sequence -/
