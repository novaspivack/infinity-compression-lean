/-
  EPIC 013 — collapse conjecture (Def 13.7 style) + T-13.8 + non-vacuity examples.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

import InfinityCompression.Meta.CompressionComposition

universe u

namespace InfinityCompression.Meta

open InfinityCompression.Core

variable {BD : Type u}

/-- Def 13.7 style — same polarity along the chain collapses to one step with matching endpoints and TC. -/
def CompressionCollapseConjecture (BD : Type u) : Prop :=
  ∀ (ch : CompressionChain BD),
    (∀ s ∈ ch.steps, s.polarity = (List.head ch.steps ch.nonempty).polarity) →
      ∃ single : CompressionInstance BD,
        single.source = (List.head ch.steps ch.nonempty).source ∧
          single.target = (List.getLast ch.steps ch.nonempty).target ∧
            (single.profile.hasTransferConcentration ↔ ch.aggregateProfile.hasTransferConcentration)

private theorem mem_head_of_nonempty (l : List (CompressionInstance BD)) (h : l ≠ []) :
    List.head l h ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as =>
    simp [List.head]

private theorem aggregate_nontrivial_of_head (ch : CompressionChain BD)
    (hnt :
      (List.head ch.steps ch.nonempty).profile.hasTransferConcentration ∨
        (List.head ch.steps ch.nonempty).profile.hasVerificationReduction) :
    ch.aggregateProfile.hasTransferConcentration ∨ ch.aggregateProfile.hasVerificationReduction := by
  rcases hnt with htc | hvr
  · left
    exact ⟨List.head ch.steps ch.nonempty, mem_head_of_nonempty ch.steps ch.nonempty, htc⟩
  · right
    exact ⟨List.head ch.steps ch.nonempty, mem_head_of_nonempty ch.steps ch.nonempty, hvr⟩

/-- T-13.8 — positive same-polarity chains admit a single-step witness with aggregate profile and TC match. -/
theorem collapse_for_same_polarity_positive_chain (ch : CompressionChain BD)
    (_h : ∀ s ∈ ch.steps, s.polarity = CompressionPolarity.positive) :
    ∃ single : CompressionInstance BD,
      single.source = (List.head ch.steps ch.nonempty).source ∧
        single.target = (List.getLast ch.steps ch.nonempty).target ∧
          (single.profile.hasTransferConcentration ↔ ch.aggregateProfile.hasTransferConcentration) := by
  let head := List.head ch.steps ch.nonempty
  have hnt := head.nontrivial
  have hagg := aggregate_nontrivial_of_head ch hnt
  refine ⟨{
      polarity := CompressionPolarity.positive
      source := head.source
      target := (List.getLast ch.steps ch.nonempty).target
      profile := ch.aggregateProfile
      nontrivial := hagg
    }, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

section Examples

private def posUnitStep : CompressionInstance Unit :=
  { polarity := CompressionPolarity.positive
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

private def negUnitStep : CompressionInstance Unit :=
  { polarity := CompressionPolarity.negative
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

private def altTwoStepChain : CompressionChain Unit :=
  { steps := [negUnitStep, posUnitStep]
    nonempty := List.cons_ne_nil _ _
    compatible := fun i => by
      fin_cases i
      simp [List.get] }

/-- NV-13.x — singleton chain is inhabited (non-vacuity). -/
example : ∃ ch : CompressionChain Unit, ch.steps.length = 1 :=
  ⟨CompressionInstance.singletonChain posUnitStep, rfl⟩

/-- NV-13.x — two-step alternating polarity chain is inhabited (non-vacuity). -/
example : ∃ ch : CompressionChain Unit, ch.steps.length = 2 ∧
    ∃ s t, s ∈ ch.steps ∧ t ∈ ch.steps ∧ s.polarity ≠ t.polarity :=
  ⟨altTwoStepChain, rfl, negUnitStep, posUnitStep, by
    refine ⟨?_, ?_, ?_⟩
    · simp [altTwoStepChain]
    · simp [altTwoStepChain]
    · intro h
      cases h⟩

end Examples

end InfinityCompression.Meta
