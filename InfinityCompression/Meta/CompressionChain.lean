/-
  EPIC 013 — `CompressionChain.aggregateProfile` + singleton embedding helpers.
-/

import Mathlib.Data.List.Basic

import InfinityCompression.Meta.CompressionInstance

universe u

namespace InfinityCompression.Meta

open InfinityCompression.Core

variable {BD : Type u}

/-- Def 13.4 — disjunctive aggregation of profile flags along a chain. -/
def CompressionChain.aggregateProfile (ch : CompressionChain BD) : CompressionProfile :=
  { hasFiniteCharacterization := ∃ s ∈ ch.steps, s.profile.hasFiniteCharacterization
    hasVerificationReduction := ∃ s ∈ ch.steps, s.profile.hasVerificationReduction
    hasTransferConcentration := ∃ s ∈ ch.steps, s.profile.hasTransferConcentration
    hasRepresentationEconomy := ∃ s ∈ ch.steps, s.profile.hasRepresentationEconomy
    hasUniformity := ∃ s ∈ ch.steps, s.profile.hasUniformity }

/-- Single-step chain from one `CompressionInstance`. -/
def CompressionInstance.singletonChain (step : CompressionInstance BD) : CompressionChain BD where
  steps := [step]
  nonempty := List.cons_ne_nil _ _
  compatible := fun i => Fin.elim0 i

end InfinityCompression.Meta
