/-
  EPIC_007_AS1 — **skeleton + extraction pairing** (honest “skeleton-dependent” carrier).

  **D-F1.4** — `SkeletonDependentExtraction` — pairs a constructive skeleton with a
  `SummitComponentExtraction`. This is the **data** that varies when one speaks of “skeleton-dependent
  extraction”; the bare `AdmissibleSummitDerivation` along `admissibleFromSkeleton` does **not** vary
  (**T-P3.7** universal collapse — `admissibleFrom_skeleton_eq_admissibleStandard`).

  **T-F1.1b** — `skeleton_dependent_toTagged_ne_of_skeleton_ne` — distinct skeletons ⇒ distinct **enriched**
  tags (`SkeletonTaggedAdmissibleSummitDerivation`), even when `H` differs.

  **T-F1.1c** — `skeleton_dependent_toTagged_admissible_eq_admissibleStandard` — the **admissible** field of
  the enriched record is still `admissibleStandard` (non-distinction at the bare record is by design).

  **scope:** bookkeeping — **defeats** “library collapse” **only** at the **enriched** / bridge layer, not
  by inventing distinct bare `AdmissibleSummitDerivation` values from `H`/`s` alone.
-/

import InfinityCompression.MetaProof.EnrichedAdmissibleSummitDerivation

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-- **D-F1.4** — Explicit skeleton + extraction pair (the dependence lives here, not in bare
  `AdmissibleSummitDerivation` equality). -/
structure SkeletonDependentExtraction {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) : Type where
  skeleton : ConstructiveDerivationSkeleton A
  H : SummitComponentExtraction A

/-- Map to the **enriched** certified layer (**T-P3.8**). -/
def SkeletonDependentExtraction.toTagged {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x : SkeletonDependentExtraction A) : SkeletonTaggedAdmissibleSummitDerivation A :=
  SkeletonTaggedAdmissibleSummitDerivation.fromExtraction x.skeleton x.H

/-- **T-F1.1c** — Bare admissible field collapses to `admissibleStandard` for every pair. -/
theorem skeleton_dependent_toTagged_admissible_eq_admissibleStandard {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (x : SkeletonDependentExtraction A) :
    x.toTagged.admissible = admissibleStandard :=
  admissibleFrom_skeleton_eq_admissibleStandard x.skeleton x.H

/-- **T-F1.1b** — Injective pairing into `SkeletonTaggedAdmissibleSummitDerivation` in the skeleton slot. -/
theorem skeleton_dependent_toTagged_ne_of_skeleton_ne {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x₁ x₂ : SkeletonDependentExtraction A) (h : x₁.skeleton ≠ x₂.skeleton) : x₁.toTagged ≠ x₂.toTagged := by
  intro heq
  exact h (congrArg SkeletonTaggedAdmissibleSummitDerivation.skeleton heq)

end InfinityCompression.MetaProof
