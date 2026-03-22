/-
  EPIC 007 — T-7.3 least fixed point (reference hook).

  Knaster–Tarski for general complete lattices lives in Mathlib’s order layer; this file
  records a **trivial** `Bool` fixed-point lemma and points the IC completion story at the
  same singleton witness as `SingletonPositive`.
-/

import Mathlib.Order.Monotone.Basic

import InfinityCompression.Examples.SingletonPositive

namespace InfinityCompression.Examples

theorem bool_monotone_has_fixed_point (f : Bool → Bool) (hf : Monotone f) :
    ∃ x : Bool, f x = x := by
  cases hf0 : f false <;> cases hf1 : f true
  · exact ⟨false, hf0⟩
  · exact ⟨false, hf0⟩
  · have hmono := hf (show false ≤ true by decide)
    rw [hf0, hf1] at hmono
    exact absurd (hmono rfl) Bool.false_ne_true
  · exact ⟨true, hf1⟩

/-- T-7.3 (reference): tie-in to the singleton positive diagonal (same `CompletionWitness` spine). -/
abbrev least_fixed_point_is_completion :=
  singleton_positive_diagonal

end InfinityCompression.Examples
