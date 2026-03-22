/-
  Program **C+** — **enriched irreducibility**: asymmetry / non-monopolarity / multiplicity live **above** the
  bare `AdmissibleSummitDerivation` carrier.

  **T-C+.4** — `autonomous_reflective_split_records_non_monopolar_standard` — an autonomous split witness
  with **standard** dependency shape records a **non–monopolar** dual-pole obligation (inherits **T-B6a.1**
  / Program E shape facts).

  **T-C+.5** — `nems_distinct_autonomous_splits_same_canonical_bare` — two distinct NEMS reflective witnesses
  share the **same** bare derivation (**T-P3.7**) but differ as **enriched** witnesses (**T-F1.1f**).

  **scope:** “Irreducibility lives upstairs” — formalized as **inequality of reflective witnesses** together
  with **equality** of the bare certified record.
-/

import InfinityCompression.MetaProof.DerivationNecessity
import InfinityCompression.MetaProof.ReflectiveSplit
import InfinityCompression.MetaProof.RoleSeparatedSkeleton
import InfinityCompression.MetaProof.SkeletonIndexedExtractionBridge

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **T-C+.4** — Along `ReflectiveSplitAutonomous`, if the recorded shape is **standard**, the recorded
  standard shape is **not** `Monopolar` (dual canonical poles are present at the semantic layer). -/
theorem autonomous_reflective_split_records_non_monopolar_standard {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (m : ReflectiveMirrorWitness A) (h : ReflectiveSplitAutonomous m)
    (hdep : m.dependencyShape = dependencyShapeStandard) : ¬ Monopolar dependencyShapeStandard := by
  rcases h with ⟨_, hauto⟩
  have hrec : RecordsDependencyShape m.bridge.derivation dependencyShapeStandard := by
    simpa [hdep] using hauto.2.2
  have hnd := records_standard_implies_non_degenerate m.bridge.derivation hrec
  exact not_monopolar_standard_record_non_degenerate m.bridge.derivation hrec hnd

/-- **T-C+.5** — Same canonical bare certification, distinct enriched autonomous mirrors (NEMS spine). -/
theorem nems_distinct_autonomous_splits_same_canonical_bare (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_1_0 H) ∧
      ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_3_2 H) ∧
        (ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_1_0 H).bridge.derivation =
          (ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_3_2 H).bridge.derivation ∧
      ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_1_0 H ≠
        ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_3_2 H :=
  ⟨reflective_split_from_roles_standard nemsRoleSkeleton_1_0 H,
    reflective_split_from_roles_standard nemsRoleSkeleton_3_2 H,
    (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard nemsRoleSkeleton_1_0 H).trans
      (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard nemsRoleSkeleton_3_2 H).symm,
    reflective_mirror_from_roles_ne_of_roles_ne nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2 H nems_role_skeletons_ne⟩

end InfinityCompression.MetaProof
