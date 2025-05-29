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

noncomputable def μ (P : ℕ → Prop) [DecidablePred P] (h : ∃ n, P n) : ℕ :=
  Nat.find h

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
/- Wₑ,ₛ = {n | n ≤ s ∧ ϕₑ,ₛ(n)↓} -/
def W_stage (e s : ℕ) : Finset ℕ :=
    (Finset.range (s)).filter (λ n => (Phi_stage e s n).isSome)
/- Wₑ = {n | n ≤ s ∧ ϕₑ(n)↓} -/
def W (e : ℕ) : Set ℕ := {n | (Phi e n).Dom}

/- ϕₑ(n)↓ ↔ ∃ (s : ℕ), ϕₑ,ₛ(n)↓ -/
theorem phi_halts_runtime_exists (e n : ℕ) : Phi_halts e n ↔ ∃ (s : ℕ), Phi_stage_halts e s n := by
  unfold Phi_stage_halts Phi_halts Phi_stage Phi
  simp [Nat.Partrec.Code.evaln_complete]
  exact exists_comm

/- s < t → ϕₑ,ₛ(n)↓ → ϕₑ,ₜ(n)↓ -/
theorem phi_halts_mono (e s t n : ℕ) (h : s ≤ t) (h1 : Phi_stage_halts e s n) :
    Phi_stage_halts e t n := by
  revert h1
  unfold Phi_stage_halts Phi_stage
  intro h1
  obtain ⟨x, hx⟩ := h1
  use x
  apply Nat.Partrec.Code.evaln_mono h hx

def runtime (e n : ℕ) : Part ℕ :=
  rfindOpt (fun s => if (Phi_stage e s n).isSome then some s else Option.none)

theorem phi_halts_runtime (e n s t : ℕ) (h1 : s ∈ (runtime e n)) :
    Phi_stage_halts e s n ∧ (t < s → Phi_stage_diverges e t n) := by
  simp [runtime, rfindOpt] at h1
  obtain ⟨⟨hs, hs2⟩, hs⟩ := h1
  unfold Phi_stage_halts
  constructor
  · rw [Option.isSome_iff_exists] at hs
    obtain ⟨a, h⟩ := hs
    use a
    exact h
  · intro h
    apply hs2 at h
    unfold Phi_stage_diverges Phi_stage_halts
    rw [h]
    simp

theorem halt_implies_runtime_gt_input (e s x n : ℕ) (h : x ∈ (Phi_stage e s n)): n < s := by
  unfold Phi_stage at h
  apply Code.evaln_bound
  exact h

lemma W_stage_phi_stage (e s n : ℕ) : n ∈ W_stage e s ↔ Phi_stage_halts e s n := by
unfold W_stage Phi_stage_halts
simp
constructor
· intro ⟨h1, h2⟩
  rw [Option.isSome_iff_exists] at h2
  exact h2
· intro h
  obtain ⟨x, h⟩ := h
  rw [Option.isSome_iff_exists]
  constructor
  · unfold Phi_stage at h
    apply Code.evaln_bound at h
    exact h
  · use x

lemma W_phi (e n : ℕ) : n ∈ W e ↔ Phi_halts e n := by
unfold W Phi_halts
exact Part.dom_iff_mem

theorem W_stage_subset_W (e s : ℕ) : (W_stage e s).toSet ⊆ W e := by
  intro x h
  simp [W_stage] at h
  simp [W]
  obtain ⟨h1, h2⟩ := h
  rw [Option.isSome_iff_exists] at h2
  obtain ⟨a, hx⟩ := h2
  refine Part.dom_iff_mem.mpr ?_
  rw [← Phi_halts]
  rw [phi_halts_runtime_exists]
  apply Exists.intro s
  apply Exists.intro a
  exact hx

theorem W_mem_iff_W_stage (e n: ℕ) : n ∈ W e ↔ ∃ (s : ℕ), n ∈ W_stage e s :=by
constructor
· intro h
  apply Part.dom_iff_mem.mp at h
  rw [← Phi_halts] at h
  rw [phi_halts_runtime_exists] at h
  obtain ⟨s, h⟩ := h
  use s
  rw [W_stage_phi_stage]
  exact h
· intro h
  obtain ⟨s, h⟩ := h
  apply W_stage_subset_W
  exact h

theorem W_eq_union_W_stage (e : ℕ) : W e = ⋃ (s : ℕ), W_stage e s := by
ext x
constructor
· intro h
  rw [W_phi, phi_halts_use_exists] at h
  obtain ⟨s, h⟩ := h
  simp
  use s
  rw [W_stage_phi_stage]
  exact h
· simp
  intro s h
  apply W_stage_subset_W
  exact h


/- Weg e s \ Weg e (s-1)-/
def W_dr (e s : ℕ) : List ℕ :=
  List.range (s + 1) |>
    List.filter (λ n => (Phi_stage e s n).isSome ∧
                         (s = 0 ∨ (Phi_stage e (s - 1) n).isNone))








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

def W_enum (e : ℕ) : ℕ →. ℕ :=
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
