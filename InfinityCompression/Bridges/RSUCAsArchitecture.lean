/-
  EPIC 014 — T-14.3: RSUC-style two-step architecture (negative sieve + positive selection).
-/

import Mathlib.Tactic

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionComposition

namespace InfinityCompression.Bridges

open InfinityCompression.Core
open InfinityCompression.Meta

private def sieve : CompressionInstance Unit :=
  { polarity := CompressionPolarity.negative
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

private def select : CompressionInstance Unit :=
  { polarity := CompressionPolarity.positive
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

def rsucChain : CompressionChain Unit :=
  { steps := [sieve, select]
    nonempty := List.cons_ne_nil _ _
    compatible := fun i => by
      fin_cases i
      simp }

/-- T-14.3 — RSUC as a two-node linear compression architecture. -/
theorem rsuc_is_architecture :
    ∃ A : CompressionArchitecture Unit rsucChain.steps.length, A = rsucChain.toArchitecture :=
  ⟨rsucChain.toArchitecture, rfl⟩

end InfinityCompression.Bridges
