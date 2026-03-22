/-
  Program **C+** — **canonical bare summit certification** after universal Phase-2 collapse.

  **D-C+.1** — `IsCanonicalBareSummitCertification` — the bare `AdmissibleSummitDerivation` is exactly the
  library summit package `admissibleStandard`.

  **T-C+.1** — `canonical_certification_principle_phase2` — every `admissibleFromSkeleton` path and every
  `fromRolesExtraction` bridge **derivation** lands in this canonical class (**T-P3.7** / **T-P3.5c**).

  **T-C+.2** — `constructed_via_extraction_implies_canonical` — `ConstructedFromArchitectureVia` forces the
  same canonical bare record.

  **scope:** This is the official “collapse is a theorem, not a bug” layer: nontrivial geometry must be
  tracked above the bare carrier (bridge / roles / enriched tags).
-/

import InfinityCompression.MetaProof.LocalToGlobalDerivation
import InfinityCompression.MetaProof.NonPackagingConstruction
import InfinityCompression.MetaProof.SkeletonIndexedExtractionBridge

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-- **D-C+.1** — Canonical bare summit certification: equality with the standard packaged record. -/
def IsCanonicalBareSummitCertification (d : AdmissibleSummitDerivation) : Prop :=
  d = admissibleStandard

theorem isCanonicalBareSummitCertification_iff (d : AdmissibleSummitDerivation) :
    IsCanonicalBareSummitCertification d ↔ d = admissibleStandard :=
  Iff.rfl

/-- **T-C+.2** — Any Phase-2 skeleton + extraction package is canonically collapsed (**T-P3.7**). -/
theorem skeleton_extraction_yields_canonical_bare {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) :
    IsCanonicalBareSummitCertification (admissibleFromSkeleton s H) :=
  admissibleFrom_skeleton_eq_admissibleStandard s H

/-- **T-C+.2** — Provenance via `ConstructedFromArchitectureVia` implies canonical bare certification. -/
theorem constructed_via_extraction_implies_canonical {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (d : AdmissibleSummitDerivation) (H : SummitComponentExtraction A)
    (h : ConstructedFromArchitectureVia A d H) : IsCanonicalBareSummitCertification d := by
  rcases h with ⟨s, rfl⟩
  exact skeleton_extraction_yields_canonical_bare s H

/-- Bridge-level packaging (roles + extraction) still yields the same canonical bare class. -/
theorem fromRoles_extraction_bridge_derivation_canonical {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    IsCanonicalBareSummitCertification (SkeletonIndexedComponentWitness.fromRolesExtraction roles H).derivation :=
  skeleton_indexed_fromRoles_derivation_eq_admissibleStandard roles H

/-- **T-C+.1** — Bundled statement of the **canonical certification principle** for the current standard bundle
  and Phase-2 interfaces. -/
theorem canonical_certification_principle_phase2 {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) :
    (∀ (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A),
        IsCanonicalBareSummitCertification (admissibleFromSkeleton s H)) ∧
      (∀ (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A),
        IsCanonicalBareSummitCertification
          (SkeletonIndexedComponentWitness.fromRolesExtraction roles H).derivation) :=
  ⟨fun s H => skeleton_extraction_yields_canonical_bare s H,
    fun roles H => fromRoles_extraction_bridge_derivation_canonical roles H⟩

end InfinityCompression.MetaProof
