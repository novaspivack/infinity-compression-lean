/-
  EPIC 014 — T-14.2: admissibility / classification cascade as `CompressionArchitecture`.
-/

import Mathlib.Tactic

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionComposition

namespace InfinityCompression.Bridges

open InfinityCompression.Core
open InfinityCompression.Meta

private def cstep (p : CompressionPolarity) : CompressionInstance Unit :=
  { polarity := p
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

/-- Negative filters → negative → positive survival (three linear steps on `Unit`). -/
def classificationCascadeChain : CompressionChain Unit :=
  let steps := [
    cstep CompressionPolarity.negative,
    cstep CompressionPolarity.negative,
    cstep CompressionPolarity.positive,
  ]
  { steps := steps
    nonempty := List.cons_ne_nil _ _
    compatible := fun i => by
      fin_cases i <;> simp }

/-- T-14.2 — classification / admissibility cascade as linear architecture. -/
theorem classification_cascade_is_architecture :
    ∃ A : CompressionArchitecture Unit classificationCascadeChain.steps.length,
      A = classificationCascadeChain.toArchitecture :=
  ⟨classificationCascadeChain.toArchitecture, rfl⟩

end InfinityCompression.Bridges
