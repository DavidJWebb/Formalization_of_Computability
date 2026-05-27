/-
Copyright (c) 2026 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/

import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Computability.Primrec.Basic
import Mathlib.Logic.Encodable.Pi

open List
open Denumerable Encodable Function Computable

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
variable {p : α → Prop} [DecidablePred p]
variable (H : Nat.Primrec fun n => Encodable.encode (@decode (List β) _ n))

@[implicit_reducible]
private def prim : Primcodable (List β) := ⟨H⟩

def ComputableRel {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop) :=
  ComputablePred fun p : α × β => s p.1 p.2

protected theorem _root_.ComputablePred.eq [DecidableEq β] {f g : α → β}
  (hf : Computable f) (hg : Computable g) :
    ComputablePred fun a => f a = g a := by
  apply Computable.computablePred
  have hEq : Computable₂ fun x y : β => decide (x = y) := (Primrec.eq (α := β)).decide.to_comp
  exact hEq.comp hf hg

namespace Computable

-- lemma of_graph
--     {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]
--     {f : α → β} (hf : Computable f) :
--     ComputablePred fun p : α × β => f p.1 = p.2 := by
--   exact ComputablePred.eq (hf.comp Primrec.fst.to_comp) (Primrec.snd.to_comp)

theorem dom_bool (f : Bool → α) : Computable f :=
  (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl

theorem dom_bool₂ (f : Bool → Bool → α) : Computable₂ f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl

protected theorem not : Computable not :=
  dom_bool _

protected theorem and : Computable₂ and :=
  dom_bool₂ _

protected theorem or : Computable₂ or :=
  dom_bool₂ _

protected theorem _root_.ComputablePred.and {p q : α → Prop} :
    (hp : ComputablePred p) → (hq : ComputablePred q) → ComputablePred fun a => p a ∧ q a
  | ⟨_, hp⟩, ⟨_, hq⟩ => computablePred <| Computable.and.comp hp hq |>.of_eq <| by simp

private theorem list_casesOn' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf : haveI := prim H; Computable f) (hg : Computable g) (hh : haveI := prim H; Computable₂ h) :
    @Computable _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have : @Computable _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
      to₂ <| option_casesOn snd (hg.comp fst)
        (hh.comp₂ (fst.comp fst).to₂ snd.to₂)).comp
      .id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by rcases f a with - | ⟨b, l⟩ <;> simp [encodek]

theorem nat_rec' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).rec (motive := fun _ => β) (g a) fun n IH => h a (n, IH) := by
  simpa using nat_rec hf hg hh

theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (h a)^[f a] (g a) := by
  have hstep : Computable₂ (fun (a : α) (p : ℕ × β) => h a p.2) :=
    hh.comp₂ ((fst : Computable fun p : α × (ℕ × β) => p.1).to₂)
      (((snd.comp snd) : Computable fun p : α × (ℕ × β) => p.2.2).to₂)
  exact (nat_rec' hf hg hstep).of_eq fun a => by
      induction f a <;>
        simp [*, -Function.iterate_succ, Function.iterate_succ']

private theorem list_foldl'
    {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : haveI := prim H; Computable f)
    (hg : Computable g)
    (hh : haveI := prim H; Computable₂ h) :
    Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  letI := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  have hG : Computable₂ G :=
    list_casesOn' H (snd.comp snd) snd
      <| to₂
      <| pair (hh.comp (fst.comp fst) (pair
        ((fst.comp snd).comp fst)
        (fst.comp snd)))
        (snd.comp snd)
  let F := fun (a : α) (n : ℕ) => (G a)^[n] (g a, f a)
  have hF : Computable fun a => (F a (encode (f a))).1 :=
    fst.comp <| nat_iterate (encode_iff.2 hf) (pair hg hf) hG
  suffices ∀ a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n) by
    refine hF.of_eq fun a => ?_
    rw [this, List.take_of_length_le (length_le_encode _)]
  introv
  dsimp only [F]
  generalize f a = l
  generalize g a = x
  induction n generalizing l x with
  | zero =>
      rfl
  | succ n IH =>
      simp only [iterate_succ, comp_apply]
      rcases l with - | ⟨b, l⟩ <;> simp [G, IH]

theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Computable f → Computable g → Computable₂ h →
      Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' (Primcodable.prim _)

theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Computable f)
    (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

theorem list_flatten : Computable (@List.flatten α) :=
  (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]

theorem list_map {f : α → List β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]

theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).flatMap (g a)) := list_flatten.comp (list_map hf hg)

theorem optionToList : Computable (Option.toList : Option α → List α) :=
  Primrec.to_comp Primrec.optionToList

theorem listFilterMap {f : α → List β} {g : α → β → Option σ}
    (hf : Computable f) (hg : Computable₂ g) : Computable fun a => (f a).filterMap (g a) :=
  (list_flatMap hf (comp₂ optionToList hg)).of_eq
    fun _ ↦ Eq.symm <| List.filterMap_eq_flatMap_toList _ _

/-- Filtering a list for elements that satisfy a decidable predicate is computable. -/
theorem listFilter {p : α → Prop} [DecidablePred p] (hf : ComputablePred p) :
    Computable fun L : List α ↦ List.filter (p ·) L := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap Computable.id
  simp only [Computable₂]
  let q : List α × α → Option α := fun x => bif decide (p x.2) then some x.2 else none
  have hq : Computable q :=
    cond ((ComputablePred.decide hf).comp snd)
    (option_some_iff.mpr snd) (const none)
  exact hq.of_eq fun x => by simp [q, Option.guard, decide_eq_true_eq]

end Computable

namespace ComputablePred

open List Primrec

variable {α β : Type*} {p : α → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- Checking if any element of a list satisfies a computable predicate is  -/
theorem exists_mem_list {p : α → Prop} [DecidablePred p] (hf : ComputablePred p) :
    ComputablePred fun L : List α ↦ ∃ a ∈ L, p a := by
  refine ⟨inferInstance, ?_⟩
  have hnonzero : Computable fun L : List α => Nat.casesOn (motive := fun _ => Bool)
        ((List.filter (fun a => p a) L).length) false (fun _ => true) :=
  nat_casesOn (list_length.comp (listFilter hf))
    (const false)
    ((const true : Computable fun _ : List α × ℕ => true).to₂)
  exact hnonzero.of_eq fun L => by
    have hiff : (∃ a ∈ L, p a) ↔ (List.filter (fun a => p a) L).length ≠ 0 := by simp
    cases hlen' : (List.filter (fun a => p a) L).length with
    | zero => simp_all
    | succ => simp_all
