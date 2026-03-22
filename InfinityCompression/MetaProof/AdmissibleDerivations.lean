/-
  EPIC_002_BH2 — B-004: **admissible summit derivation** surrogate.

  Not a Lean proof term or `Proof` object: a record of a `SummitBundle` together with **witnesses**
  that each field holds, used for Route B dependency statements.
-/

import InfinityCompression.MetaProof.DependencyShape

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier

/-- **D-B4.1** — Surrogate for an admissible derivation of summit content: a bundle plus proofs of
  its `Prop` fields. -/
structure AdmissibleSummitDerivation where
  bundle : SummitBundle
  /-- Witness for the anatomy/amalg shard. -/
  anatomyWitness : bundle.anatomyAmalg
  /-- Witness for the internal UL-3/4 shard. -/
  internalWitness : bundle.internalUl34

/-- Well-formed: the interpreted summit proposition holds (equivalently: both witnesses combine). -/
def WellFormedAdmissible (d : AdmissibleSummitDerivation) : Prop :=
  interpretSummitBundle d.bundle

lemma wellFormed_iff (d : AdmissibleSummitDerivation) :
    WellFormedAdmissible d ↔ interpretSummitBundle d.bundle :=
  Iff.rfl

theorem wellFormed_of_components (d : AdmissibleSummitDerivation) :
    WellFormedAdmissible d :=
  ⟨d.anatomyWitness, d.internalWitness⟩

/-- **D-B4.3** — Records a shape when the bundle’s fields **coincide** with the shape obligations and
  both shard witnesses hold (so the shape’s implicational clauses are satisfied). -/
def RecordsDependencyShape (d : AdmissibleSummitDerivation) (shape : SummitDependencyShape) : Prop :=
  shape.requiresPositiveCore = d.bundle.anatomyAmalg ∧
    shape.requiresNegativeFrontier = d.bundle.internalUl34 ∧
    shape.requiresInternalCompletion = d.bundle.internalUl34 ∧
    shape.excludesTotalization = d.bundle.internalUl34 ∧
    shape.requiresPolarityOrganization = interpretSummitBundle d.bundle ∧
    d.bundle.anatomyAmalg ∧
    d.bundle.internalUl34

/-- **D-B4.2** — Standard admissible derivation from the library summit proof. -/
def admissibleStandard : AdmissibleSummitDerivation where
  bundle := summitBundleStandard
  anatomyWitness := ic_summit_anatomy_and_amalgamation_obstruction
  internalWitness := ic_summit_internal_compression_ul34

theorem admissibleStandard_wellFormed : WellFormedAdmissible admissibleStandard :=
  ic_universal_theorem_summit

theorem admissibleStandard_records_standard_shape :
    RecordsDependencyShape admissibleStandard dependencyShapeStandard := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rfl
  · exact ic_summit_anatomy_and_amalgamation_obstruction
  · exact ic_summit_internal_compression_ul34

end InfinityCompression.MetaProof
