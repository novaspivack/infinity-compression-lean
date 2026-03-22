/-
  EPIC_002_BH2 — B-005: first **Route B** meta-theorem milestone.

  **T-B5.1** — Any well-formed admissible derivation that **records** the standard dependency shape
  must realize both meta-poles (positive core + negative frontier), i.e. the two named summit shards.
-/

import InfinityCompression.MetaProof.AdmissibleDerivations

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier

/-- **T-B5.1** — Option A: from recording the standard shape, the two pole obligations hold.

  The proof uses the witness fields `anatomyWitness` / `internalWitness` only indirectly: `RecordsDependencyShape`
  requires the bundle propositions to match the shape and to hold; we transport along the equalities. -/
theorem summit_requires_dual_poles (d : AdmissibleSummitDerivation)
    (_h : WellFormedAdmissible d)
    (hrec : RecordsDependencyShape d dependencyShapeStandard) :
    dependencyShapeStandard.requiresPositiveCore ∧ dependencyShapeStandard.requiresNegativeFrontier := by
  rcases hrec with ⟨ePos, eNeg, _, _, _, ha, hi⟩
  exact ⟨ePos ▸ ha, eNeg ▸ hi⟩

/-- Same conclusion for the **standard** admissible derivation (corollary packaging). -/
theorem summit_requires_dual_poles_standard :
    dependencyShapeStandard.requiresPositiveCore ∧ dependencyShapeStandard.requiresNegativeFrontier :=
  summit_requires_dual_poles admissibleStandard admissibleStandard_wellFormed
    admissibleStandard_records_standard_shape

/-- The two poles jointly imply the minimal §2.5 summit proposition. -/
theorem dual_poles_imply_ic_universal_summit :
    dependencyShapeStandard.requiresPositiveCore ∧ dependencyShapeStandard.requiresNegativeFrontier →
      icUniversalSummitStatement :=
  id

end InfinityCompression.MetaProof
