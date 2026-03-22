/-
  EPIC_005-C — **enriched certified** layer: **Type-valued** skeleton tag alongside
  `AdmissibleSummitDerivation` (EPIC_005 reformulation after **T-P3.7**).

  **D-P3.8** — `SkeletonTaggedAdmissibleSummitDerivation` — tag survives where bare record collapses.

  **T-P3.8** — `skeleton_tagged_ne_of_skeleton_ne`, `nems_skeleton_tagged_fromExtraction_distinct` —
  distinct constructive skeletons ⇒ distinct enriched records (even when `admissible` is **equal** as
  `AdmissibleSummitDerivation` for fixed `H` — **T-P3.7**).

  **scope:** enrichment — not a contradiction of **T-P3.7**; carries skeleton in **data**, not in `Prop`
  witnesses alone.
-/

import InfinityCompression.MetaProof.LocalToGlobalDerivation
import InfinityCompression.MetaProof.RoleSeparatedSkeleton

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-P3.8** — `AdmissibleSummitDerivation` paired with a **Type-valued** `ConstructiveDerivationSkeleton`
  tag. This is the minimal **enriched certified type** for EPIC_005-C (vs bare `AdmissibleSummitDerivation`). -/
structure SkeletonTaggedAdmissibleSummitDerivation {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) :
    Type where
  skeleton : ConstructiveDerivationSkeleton A
  admissible : AdmissibleSummitDerivation

/-- Phase 2 path with explicit tag — `admissible` is `admissibleFromSkeleton s H` (**T-P3.7** / **T-P3.5c**). -/
def SkeletonTaggedAdmissibleSummitDerivation.fromExtraction {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) :
    SkeletonTaggedAdmissibleSummitDerivation A where
  skeleton := s
  admissible := admissibleFromSkeleton s H

/-- **T-P3.8** — Injective in `skeleton` when `admissible` is fixed (tag carries the distinction). -/
theorem skeleton_tagged_ne_of_skeleton_ne {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (s₁ s₂ : ConstructiveDerivationSkeleton A) (d : AdmissibleSummitDerivation) (h : s₁ ≠ s₂) :
    (⟨s₁, d⟩ : SkeletonTaggedAdmissibleSummitDerivation A) ≠ ⟨s₂, d⟩ := by
  intro heq
  exact h (congrArg SkeletonTaggedAdmissibleSummitDerivation.skeleton heq)

/-- **T-P3.8** — NEMS: two distinct enriched tags for the **same** extraction `H` (bare `admissible`
  is **equal** between them — **T-P3.7** — but the **enriched** records differ). -/
theorem nems_skeleton_tagged_fromExtraction_distinct (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    SkeletonTaggedAdmissibleSummitDerivation.fromExtraction nemsRoleSkeleton_1_0.toConstructiveSkeleton H ≠
      SkeletonTaggedAdmissibleSummitDerivation.fromExtraction nemsRoleSkeleton_3_2.toConstructiveSkeleton H := by
  intro h
  exact nems_role_constructive_skeletons_ne (congrArg SkeletonTaggedAdmissibleSummitDerivation.skeleton h)

end InfinityCompression.MetaProof
