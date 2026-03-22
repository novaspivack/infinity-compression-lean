/-
  EPIC_002_BH2 — B-003: **dependency-shape** language for Route B.

  **Meta-poles** (positive core vs negative/internal frontier) are *not* `CompressionPolarity`; they
  label which **summit shard** family a dependency record refers to.
-/

import InfinityCompression.MetaProof.SummitTargets

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier

/-- **D-B3.1** — Dependency shape: each field is the **library proposition** that plays the named
  role in the current IC summit story.

  * `requiresPositiveCore` — UL-2 fragment + UL-1-style amalgamation obstruction (`ic_summit_anatomy_and_amalgamation_obstruction`).
  * `requiresNegativeFrontier` — UL-3/UL-4 diagonal bundle on the NV-28 family (`ic_summit_internal_compression_ul34`).
  * `requiresInternalCompletion` — at this layer, identified with the internal UL-3/4 shard (same as negative frontier pole).
  * `excludesTotalization` — same shard: internal compression without a uniform completion operator class.
  * `requiresPolarityOrganization` — full minimal §2.5 summit (both shards): the library’s packaged conjunction. -/
structure SummitDependencyShape where
  requiresPositiveCore : Prop
  requiresNegativeFrontier : Prop
  requiresInternalCompletion : Prop
  excludesTotalization : Prop
  requiresPolarityOrganization : Prop

/-- **D-B3.2** — Standard shape: obligations are **exactly** the named summit shards and their conjunction. -/
def dependencyShapeStandard : SummitDependencyShape where
  requiresPositiveCore := icUniversalSummitStatementAnatomyAmalg
  requiresNegativeFrontier := icUniversalSummitStatementInternalUl34
  requiresInternalCompletion := icUniversalSummitStatementInternalUl34
  excludesTotalization := icUniversalSummitStatementInternalUl34
  requiresPolarityOrganization := icUniversalSummitStatement

lemma dependencyShapeStandard_positive_pole :
    dependencyShapeStandard.requiresPositiveCore = icUniversalSummitStatementAnatomyAmalg :=
  rfl

lemma dependencyShapeStandard_negative_pole :
    dependencyShapeStandard.requiresNegativeFrontier = icUniversalSummitStatementInternalUl34 :=
  rfl

/-- **D-B3.3** — A bundle **satisfies** a shape when each shape obligation is **logically** implied by
  the corresponding bundle fields. -/
def SatisfiesDependencyShape (shape : SummitDependencyShape) (b : SummitBundle) : Prop :=
  (shape.requiresPositiveCore → b.anatomyAmalg) ∧
    (shape.requiresNegativeFrontier → b.internalUl34) ∧
    (shape.requiresInternalCompletion → b.internalUl34) ∧
    (shape.excludesTotalization → b.internalUl34) ∧
    (shape.requiresPolarityOrganization → interpretSummitBundle b)

theorem summitBundleStandard_satisfies_standard_shape :
    SatisfiesDependencyShape dependencyShapeStandard summitBundleStandard := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact h
  · exact h
  · exact h
  · exact h
  · exact h

/-- **T-B3.1** — Standard dependency shape is **exactly** the two named summit shards (S3 / biconditional layer). -/
theorem standard_shape_matches_summit_iff :
    icUniversalSummitStatement ↔
      dependencyShapeStandard.requiresPositiveCore ∧ dependencyShapeStandard.requiresNegativeFrontier :=
  Iff.rfl

/-- **D-B3.4** — Same content as `ic_universal_theorem_summit_iff_components`, phrased with meta-pole names. -/
theorem standard_shape_matches_summit_iff_components :
    icUniversalSummitStatement ↔
      (dependencyShapeStandard.requiresPositiveCore ∧ dependencyShapeStandard.requiresNegativeFrontier) :=
  ic_universal_theorem_summit_iff_components

end InfinityCompression.MetaProof
