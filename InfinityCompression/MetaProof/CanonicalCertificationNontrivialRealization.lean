/-
  Program **C+** — **canonical certification + nontrivial enriched realization** (flagship packaging).

  **T-C+.6** — `crown_eligible_nems_exists_reflective_split_nontrivial_enriched_pair` — on the crown-eligible
  NEMS spine, there exist **two** autonomous reflective splits that share the **same** bare summit
  certification but are **distinct** as enriched witnesses.

  **T-C+.7** — `two_distinct_roles_nontrivial_enriched_pair` — abstract pattern: any **two** distinct
  `RoleSeparatedSkeleton` values with fixed `H` yield the same phenomenon.

  **scope:** This is the formal “summit is canonical at certification; realization is nontrivial upstairs”
  theorem — **not** bare-record inequality.
-/

import InfinityCompression.MetaProof.CrownEligible
import InfinityCompression.MetaProof.EnrichedIrreducibility
import InfinityCompression.MetaProof.SkeletonIndexedExtractionBridge

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-- **T-C+.7** — Distinct role skeletons ⇒ a pair of **ReflectiveSplitAutonomous** witnesses with equal bare
  derivation and unequal enriched witnesses. -/
theorem two_distinct_roles_nontrivial_enriched_pair {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A) (hne : roles₁ ≠ roles₂) :
    ∃ m₁ m₂ : ReflectiveMirrorWitness A,
      ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
        m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂ :=
  let m₁ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H
  let m₂ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H
  ⟨m₁, m₂,
    reflective_split_from_roles_standard roles₁ H,
    reflective_split_from_roles_standard roles₂ H,
    (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard roles₁ H).trans
      (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard roles₂ H).symm,
    reflective_mirror_from_roles_ne_of_roles_ne roles₁ roles₂ H hne⟩

/-- **T-C+.6** — Crown-eligible NEMS spine: canonical bare summit class, **nontrivial** enriched pair. -/
theorem crown_eligible_nems_exists_reflective_split_nontrivial_enriched_pair
    (_h : CrownEligible nemsSpineChain.toArchitecture) :
    ∃ m₁ m₂ : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
      ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
        m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂ := by
  simpa using
    two_distinct_roles_nontrivial_enriched_pair nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2
      (librarySummitExtraction nemsSpineChain.toArchitecture) nems_role_skeletons_ne

/-- Packaging: NEMS instance of the nontrivial pair (explicit `H`). -/
theorem nems_reflective_split_nontrivial_enriched_pair (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ∃ m₁ m₂ : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
      ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
        m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂ :=
  two_distinct_roles_nontrivial_enriched_pair nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2 H nems_role_skeletons_ne

end InfinityCompression.MetaProof
