/-
  EPIC_005_RK7 — **bridge layer** between role-separated skeletons and the Phase 2 admissible interface.

  **D-P3.5** — `SkeletonIndexedComponentWitness`: role assignment + extraction + canonical constructive
  skeleton + resulting `AdmissibleSummitDerivation`.

  **T-P3.5** — `skeleton_indexed_witness_wellFormed`, `skeleton_indexed_witness_constructed_via` — every
  bridge witness maps into the admissible interface (well-formed + `ConstructedFromArchitectureVia`).

  **T-P3.5b** — `skeleton_indexed_fromRoles_injective_roles` / `skeleton_indexed_fromRoles_ne_of_roles_ne` —
  for fixed extraction, distinct roles ⇒ distinct **bridge** records (multiplicity below full
  `MetaSummitWitness`).

  **T-P3.5c** — `skeleton_indexed_fromRoles_derivation_eq_admissibleStandard` — **any** extraction collapses
  the **derivation** field to `admissibleStandard` (**T-P3.7** universal collapse; **T-P2.7** is the
  definitional special case for `librarySummitExtraction`); distinctness is in the indexed witness, not in
  bare `AdmissibleSummitDerivation` equality.

  **T-P3.6** — `nems_skeleton_indexed_witnesses_distinct` — two distinct bridge witnesses on the NEMS spine
  with shared `librarySummitExtraction`.

  **D-P3.9** — `ExternalSummitCertificate` — alias for **`SkeletonIndexedComponentWitness`** (spec name for
  the **external** certificate layer).

  **scope: bridge** — strictly between bare admissible records and provenance-only meta-wrap; does **not**
  defeat **T-P2.7** at the derivation field under library extraction.
-/

import InfinityCompression.MetaProof.AdmissibleDerivations
import InfinityCompression.MetaProof.LocalToGlobalDerivation
import InfinityCompression.MetaProof.NonPackagingConstruction
import InfinityCompression.MetaProof.RoleSeparatedSkeleton

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-P3.5** — Role poles + extraction + induced constructive skeleton + admissible record along the
  Phase 2 path. -/
structure SkeletonIndexedComponentWitness {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) :
    Type where
  roles : RoleSeparatedSkeleton A
  H : SummitComponentExtraction A
  /-- Canonical constructive skeleton from the role poles (`RoleSeparatedSkeleton.toConstructiveSkeleton`). -/
  toSkeleton : ConstructiveDerivationSkeleton A
  skeleton_eq : toSkeleton = roles.toConstructiveSkeleton
  /-- Derived admissible record. -/
  derivation : AdmissibleSummitDerivation
  derivation_eq : derivation = admissibleFromSkeleton toSkeleton H

/-- Canonical bridge witness from roles + extraction (no extra data).
  Named `fromRolesExtraction` to avoid clashing with the structure’s generated `mk`. -/
def SkeletonIndexedComponentWitness.fromRolesExtraction {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    SkeletonIndexedComponentWitness A where
  roles := roles
  H := H
  toSkeleton := roles.toConstructiveSkeleton
  skeleton_eq := rfl
  derivation := admissibleFromSkeleton (roles.toConstructiveSkeleton) H
  derivation_eq := rfl

/-- **T-P3.5** — Well-formedness of the derived admissible record. -/
theorem skeleton_indexed_witness_wellFormed {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (w : SkeletonIndexedComponentWitness A) : WellFormedAdmissible w.derivation := by
  rw [w.derivation_eq]
  exact wellFormed_admissibleFromSkeleton w.toSkeleton w.H

/-- **T-P3.5** — Provenance: the derivation arises from the exhibited skeleton and extraction. -/
theorem skeleton_indexed_witness_constructed_via {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (w : SkeletonIndexedComponentWitness A) : ConstructedFromArchitectureVia A w.derivation w.H :=
  ⟨w.toSkeleton, w.derivation_eq⟩

/-- **T-P3.5b** — For fixed `H`, `fromRolesExtraction` is injective in `roles`. -/
theorem skeleton_indexed_fromRoles_injective_roles {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    SkeletonIndexedComponentWitness.fromRolesExtraction roles₁ H =
        SkeletonIndexedComponentWitness.fromRolesExtraction roles₂ H →
      roles₁ = roles₂ := by
  intro heq
  exact congrArg SkeletonIndexedComponentWitness.roles heq

/-- **T-P3.5b** — Distinct roles ⇒ distinct bridge witnesses (same extraction). -/
theorem skeleton_indexed_fromRoles_ne_of_roles_ne {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) (h : roles₁ ≠ roles₂) :
    SkeletonIndexedComponentWitness.fromRolesExtraction roles₁ H ≠
        SkeletonIndexedComponentWitness.fromRolesExtraction roles₂ H :=
  fun heq => h (skeleton_indexed_fromRoles_injective_roles roles₁ roles₂ H heq)

/-- **T-P3.5c** — `fromRolesExtraction` always yields `derivation = admissibleStandard` (**T-P3.7** universal
  collapse), for **any** `SummitComponentExtraction`. -/
theorem skeleton_indexed_fromRoles_derivation_eq_admissibleStandard {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    (SkeletonIndexedComponentWitness.fromRolesExtraction roles H).derivation = admissibleStandard := by
  dsimp [SkeletonIndexedComponentWitness.fromRolesExtraction]
  exact admissibleFrom_skeleton_eq_admissibleStandard roles.toConstructiveSkeleton H

/-- **T-P3.5c** (library packaging) — Under `librarySummitExtraction`, the **derivation** field is
  `admissibleStandard` (**T-P2.7** definitionally; also an instance of **T-P3.7**). -/
theorem admissible_skeleton_indexed_library_eq_standard {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles : RoleSeparatedSkeleton A) :
    (SkeletonIndexedComponentWitness.fromRolesExtraction roles (librarySummitExtraction A)).derivation =
      admissibleStandard :=
  skeleton_indexed_fromRoles_derivation_eq_admissibleStandard _ _

/-- **T-P3.6** — NEMS: two distinct bridge witnesses with the same library extraction. -/
theorem nems_skeleton_indexed_witnesses_distinct :
    SkeletonIndexedComponentWitness.fromRolesExtraction nemsRoleSkeleton_1_0 (librarySummitExtraction _) ≠
      SkeletonIndexedComponentWitness.fromRolesExtraction nemsRoleSkeleton_3_2 (librarySummitExtraction _) :=
  skeleton_indexed_fromRoles_ne_of_roles_ne _ _ _ nems_role_skeletons_ne

/-- **D-P3.9** — Spec / search alias: **external** summit certificate — role + extraction + skeleton +
  `derivation` — where distinction survives **T-P3.7** on the bare `admissible` field. -/
abbrev ExternalSummitCertificate {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) : Type :=
  SkeletonIndexedComponentWitness A

end InfinityCompression.MetaProof
