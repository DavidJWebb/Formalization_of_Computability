/- Lemmata that are correct, but aren't needed anywhere (yet?) -/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical

lemma List.count_pos_of_mem {α : Type*} [DecidableEq α] {a : α} {L : List α}
    (h : a ∈ L) : 0 < List.count a L := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.count, List.mem_cons] at *
    cases h <;> simp_all
