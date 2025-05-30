/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import FormalizationOfComputability.SetPrimRec
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Linarith

set_option warningAsError false

/-
# Encoding and Decoding
A lemma that encoding and decoding a natural number results in
the same partial recursive function, so that the two truly are
inverses of one another
-/

namespace Nat.Partrec.Code

lemma encode_inverse_eval (c : Code) :
    c = (Code.ofNatCode (Code.encodeCode c))  := by
  induction c with
  | zero => simp [Code.encodeCode, Code.ofNatCode, Code.eval]
  | succ => simp [Code.encodeCode, Code.ofNatCode, Code.eval]
  | left => simp [Code.encodeCode, Code.ofNatCode, Code.eval]
  | right => simp [Code.encodeCode, Code.ofNatCode, Code.eval]
  | pair cf cg ihf ihg =>
      simp [Code.encodeCode, Code.ofNatCode, Code.eval]
      constructor
      · exact ihf
      · exact ihg
  | comp cf cg ihf ihg =>
      simp [Code.encodeCode, Code.ofNatCode, Code.eval]
      constructor
      · exact ihf
      · exact ihg
  | prec cf cg ihf ihg =>
      simp [Code.encodeCode, Code.ofNatCode, Code.eval]
      constructor
      · exact ihf
      · exact ihg
  | rfind' cf ihf =>
      simp [Code.encodeCode, Code.ofNatCode, Code.eval]
      exact ihf
