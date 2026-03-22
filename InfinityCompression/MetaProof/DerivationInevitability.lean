/-
  EPIC_003_BH6 — B-008: **derivation inevitability** / minimality for standard dual-pole shapes.
-/

import InfinityCompression.MetaProof.DerivationNecessity

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier

/-- **D-B8.1** — Minimal dual-pole shape: matches both canonical shard props and the full §2.5 conjunction. -/
def MinimalSummitDependencyShape (shape : SummitDependencyShape) : Prop :=
  shape.requiresPositiveCore = icUniversalSummitStatementAnatomyAmalg ∧
    shape.requiresNegativeFrontier = icUniversalSummitStatementInternalUl34 ∧
      shape.requiresPolarityOrganization = icUniversalSummitStatement

/-- **T-B8.1** — The standard shape is minimal in this sense. -/
theorem dependencyShapeStandard_minimal : MinimalSummitDependencyShape dependencyShapeStandard :=
  ⟨rfl, rfl, rfl⟩

/-- Matching both shards **and** the full summit conjunct as `requiresPolarityOrganization`. -/
theorem minimal_of_matching_dual_shards (shape : SummitDependencyShape)
    (hpos : shape.requiresPositiveCore = icUniversalSummitStatementAnatomyAmalg)
    (hneg : shape.requiresNegativeFrontier = icUniversalSummitStatementInternalUl34)
    (horg : shape.requiresPolarityOrganization = icUniversalSummitStatement) :
    MinimalSummitDependencyShape shape :=
  ⟨hpos, hneg, horg⟩

end InfinityCompression.MetaProof
