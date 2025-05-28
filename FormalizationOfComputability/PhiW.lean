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

/- Wₑ,ₛ = {n | n ≤ s ∧ ϕₑ,ₛ(n)↓}, with useful computational content:
membership is decidable, for instance-/
def Weg_stage (e s : ℕ) : Finset ℕ :=
    (Finset.range (s + 1)).filter (λ n => (Phi_stage e s n).isSome)

/- Wₑ = {n | n ≤ s ∧ ϕₑ(n)↓} -/
def Weg (e : ℕ) : Set ℕ := {n | (Phi e n).Dom}


-- Views Of Mount Σ01 :
-- partial recursive f
-- its domain X
-- the range of a computable g : ℕ → ℕ
-- the code e for f
-- the (possibly finite) sequence of nth outputs {fn}
-- the infinite partial recursive sequence of nth outputs {fn}


-- lemma : an increasing Sigma01 sequence is Delta01-+-

/-
x ∈ c.eval n ↔ ∃ (k : ℕ), x ∈ evaln k c n Nat.Partrec.Code.evaln_complete
c.eval x = 1 ↔ ϕ ∃ s = (μ t) evaln x c t = 1 (essentially, s = the stage ϕₑ(x) halts)
## evaln x c s = ϕ_{c,s}(x)
W_{e,s} = {n | n≤s ∧ evaln x e s = 1}

Now we can build W_{e,s} in the order things are enumerated!

s0 = μ t W_{e,t} ≠ ∅           (the least stage when an element is enumerated into W_{e,t})
n0 = μ x evaln x e s0 = 1      (the least element of W_{e,s0})
s (n) = μ t W_{e,t} ≠ {s0, ..., s(n-1)} (the least stage when something new enters W_e)

Note the above handles the case that multiple elements enter at the same stage - W_{e,t}
will not equal the full set until every new element has been included

i n = μ s(n) ∀ (m : ℕ), (m < n) → s(m) < s(n)
That is, the i n are an increasing sequence -/
