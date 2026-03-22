/-
  EPIC_007_AS1 — **proof-relevant reflective mirror witness** (post-summit layer).

  **D-F1.1** — `ReflectiveMirrorWitness` — packages **role-separated** poles, the Phase-2 bridge
  (`SkeletonIndexedComponentWitness`), and standard-shape satisfaction at the bridge’s `derivation`.

  **D-F1.2** — `ConstructedWithoutStandardSummitRoute` — **positive provenance**: the bridge is **exactly**
  `fromRolesExtraction` on the packaged `roles` and `H` (not a free-floating `admissibleStandard` pick).

  **D-F1.3** — `AutonomousSummitMirror` — well-formed + standard shape recording + the provenance predicate.

  **Honesty (epistemology):** Shard witnesses **inside** `SummitComponentExtraction` may still be the
  library **component lemmas** (as in `librarySummitExtraction`). That is **not** yet a
  skeleton-dependent extraction that defeats **T-P2.7** / **T-P3.5c**; the **gain** here is a **typed**
  carrier with **distinct** `RoleSeparatedSkeleton` multiplicity (**T-P3.5b**-style) and an explicit
  **Phase-2 assembly** path, audited separately from “`exact admissibleStandard` in one step.”

  **Program C+** (`CanonicalCertification.lean`, `ReflectiveSplit.lean`, `EnrichedIrreducibility.lean`) treats
  bare-record collapse as a **theorem** and formalizes multiplicity in **roles** / enriched witnesses.

  See `specs/IN-PROCESS/EPIC_007_AS1_SUMMIT_INDEPENDENT_REFLECTIVE_MIRROR_SPEC.md`.
-/

import InfinityCompression.MetaProof.DependencyShape
import InfinityCompression.MetaProof.SkeletonIndexedExtractionBridge

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-F1.1** — Reflective mirror witness: role poles + **bridge** + **standard** shape bookkeeping. -/
structure ReflectiveMirrorWitness {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) where
  roles : RoleSeparatedSkeleton A
  bridge : SkeletonIndexedComponentWitness A
  /-- Bridge’s canonical skeleton agrees with the role-induced constructive skeleton. -/
  skeleton_agrees : bridge.toSkeleton = roles.toConstructiveSkeleton
  dependencyShape : SummitDependencyShape
  /-- Shape satisfied by the bridge’s `derivation.bundle`. -/
  recordsShape : SatisfiesDependencyShape dependencyShape bridge.derivation.bundle

/-- **D-F1.2** — Positive provenance: `fromRolesExtraction` on the witness’s own `roles` and `H`. -/
def ConstructedWithoutStandardSummitRoute {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (m : ReflectiveMirrorWitness A) : Prop :=
  m.bridge = SkeletonIndexedComponentWitness.fromRolesExtraction m.roles m.bridge.H

/-- **D-F1.3** — Autonomous mirror (EPIC_007 — first packaging; compare `SummitCapableMirror` in Program E). -/
def AutonomousSummitMirror {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (m : ReflectiveMirrorWitness A) : Prop :=
  ConstructedWithoutStandardSummitRoute m ∧
    WellFormedAdmissible m.bridge.derivation ∧
      RecordsDependencyShape m.bridge.derivation m.dependencyShape

/-- Assemble a witness from roles + extraction, using the **standard** dependency shape (bundle is always
  `summitBundleStandard` along `admissibleFromSkeleton`). -/
def ReflectiveMirrorWitness.fromRolesAndExtraction_standard {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    ReflectiveMirrorWitness A :=
  let br := SkeletonIndexedComponentWitness.fromRolesExtraction roles H
  { roles := roles
    bridge := br
    skeleton_agrees := br.skeleton_eq
    dependencyShape := dependencyShapeStandard
    recordsShape := by
      simpa [br, SkeletonIndexedComponentWitness.fromRolesExtraction, admissibleFromSkeleton] using
        summitBundleStandard_satisfies_standard_shape }

theorem reflective_mirror_skeleton_eq_roles {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H).roles = roles :=
  rfl

/-- **T-F1.1e** — `fromRolesAndExtraction_standard` is injective in `roles` (fixed extraction). All
  multiplicity of reflective realization is carried by **roles** / bridge, not by bare `AdmissibleSummitDerivation`. -/
theorem reflective_mirror_from_roles_injective_roles {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H =
        ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H →
      roles₁ = roles₂ :=
  congrArg ReflectiveMirrorWitness.roles

/-- **T-F1.1f** — Distinct role skeletons ⇒ distinct reflective witnesses (same `H`). -/
theorem reflective_mirror_from_roles_ne_of_roles_ne {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) (h : roles₁ ≠ roles₂) :
    ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H ≠
      ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H := by
  intro heq
  exact h (reflective_mirror_from_roles_injective_roles roles₁ roles₂ H heq)

/-- **T-F1.1d** (bridge field) — Despite distinct **roles** / skeleton multiplicity, the packaged
  `AdmissibleSummitDerivation` is still `admissibleStandard` (**T-P3.5c** / **T-P3.7**). Non-collapse is
  tracked in `ReflectiveMirrorWitness.roles` and in **enriched** layers (`SkeletonDependentExtraction`), not
  in bare derivation inequality. -/
theorem reflective_mirror_bridge_derivation_eq_admissibleStandard {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H).bridge.derivation = admissibleStandard :=
  skeleton_indexed_fromRoles_derivation_eq_admissibleStandard roles H

/-- **T-F1.1a** — `fromRolesAndExtraction_standard` satisfies **AutonomousSummitMirror** hypotheses. -/
theorem autonomous_mirror_from_roles_extraction_standard {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) :
    AutonomousSummitMirror (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact skeleton_indexed_witness_wellFormed _
  · simpa [ReflectiveMirrorWitness.fromRolesAndExtraction_standard, dependencyShapeStandard] using
      records_dependency_shape_admissibleFromSkeleton (roles.toConstructiveSkeleton) H

end InfinityCompression.MetaProof
