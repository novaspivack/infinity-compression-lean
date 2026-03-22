/-
  EPIC 013 (initial segment) — compression instances, chains, Theorem 6.2 complementarity
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases

import InfinityCompression.Core.CompressionProfile

universe u

namespace InfinityCompression.Meta

open InfinityCompression.Core

inductive CompressionPolarity where
  | positive
  | negative
  | limit

namespace CompressionPolarity

/-- Used in `RoleSeparatedSkeleton.toConstructiveSkeleton` polarity-separation proof. -/
theorem pos_ne_negative : positive ≠ negative := by
  intro h
  cases h

end CompressionPolarity

structure CompressionInstance (BurdenDesc : Type u) where
  polarity : CompressionPolarity
  source : BurdenDesc
  target : BurdenDesc
  profile : CompressionProfile
  nontrivial : profile.hasTransferConcentration ∨ profile.hasVerificationReduction

private theorem nat_pred_lt_self {n : ℕ} (hn : 0 < n) : n - 1 < n := by
  cases n with
  | zero => cases hn
  | succ n => simp

private theorem val_lt_length_of_fin_pred {n : ℕ} (hn : 0 < n) (i : Fin (n - 1)) : i.val < n :=
  Nat.lt_trans i.is_lt (nat_pred_lt_self hn)

private theorem val_succ_lt_length_of_fin_pred {n : ℕ} (hn : 0 < n) (i : Fin (n - 1)) :
    i.val + 1 < n := by
  cases n with
  | zero => cases hn
  | succ n =>
    cases n with
    | zero =>
      simp at i
      exact Fin.elim0 i
    | succ n =>
      exact Nat.succ_lt_succ_iff.mpr i.is_lt

structure CompressionChain (BurdenDesc : Type u) where
  steps : List (CompressionInstance BurdenDesc)
  nonempty : steps ≠ []
  compatible :
    ∀ i : Fin (steps.length - 1),
      (steps.get ⟨i.val, val_lt_length_of_fin_pred (List.length_pos_of_ne_nil nonempty) i⟩).target =
        (steps.get ⟨i.val + 1, val_succ_lt_length_of_fin_pred (List.length_pos_of_ne_nil nonempty) i⟩).source

/-- **Theorem 6.2** — two compatible steps of opposite polarity form a chain. -/
theorem polarity_complementarity {BD : Type u}
    (negStep posStep : CompressionInstance BD)
    (_ : negStep.polarity = CompressionPolarity.negative)
    (_ : posStep.polarity = CompressionPolarity.positive)
    (hComp : negStep.target = posStep.source) :
    ∃ ch : CompressionChain BD, ch.steps = [negStep, posStep] := by
  refine ⟨{
    steps := [negStep, posStep]
    nonempty := by simp
    compatible := ?_
  }, rfl⟩
  intro i
  fin_cases i
  simp [List.get, hComp]

end InfinityCompression.Meta
