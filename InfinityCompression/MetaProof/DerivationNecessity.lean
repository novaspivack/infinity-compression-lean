/-
  EPIC_003_BH6 — B-006a: **derivation necessity** strengthening (Route B Level 2).

  **scope: semantic** — `Monopolar` / `NonDegenerateAdmissible` classify shapes and bundles; **T-B6a.1**
  extracts that a recorded shape matching both canonical summit shards cannot be “monopolar” in the
  sense defined here (missing a canonical pole obligation).

  **Program C+** — `CanonicalCertification.lean` packages bare-record collapse as
  `IsCanonicalBareSummitCertification`; non-monopolarity **survives** on standard recording via this layer
  and on **enriched** reflective witnesses (`EnrichedIrreducibility.lean`).
-/

import InfinityCompression.MetaProof.AdmissibleDerivations

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier

/-- Both meta-pole obligations match the **named** §2.5 shard propositions (dual-pole / biconditional layer). -/
def HasCanonicalDualPoleShape (shape : SummitDependencyShape) : Prop :=
  shape.requiresPositiveCore = icUniversalSummitStatementAnatomyAmalg ∧
    shape.requiresNegativeFrontier = icUniversalSummitStatementInternalUl34

/-- **D-B6a.1** — “Monopolar” surrogate: the shape does **not** carry both canonical pole obligations.
  (This is *not* a claim about `CompressionPolarity`.) -/
def Monopolar (shape : SummitDependencyShape) : Prop :=
  ¬ HasCanonicalDualPoleShape shape

/-- **D-B6a.2** — Non-degenerate: bundle fields are exactly the two named summit shards (full semantic
  content at this layer). -/
def NonDegenerateAdmissible (d : AdmissibleSummitDerivation) : Prop :=
  d.bundle.anatomyAmalg = icUniversalSummitStatementAnatomyAmalg ∧
    d.bundle.internalUl34 = icUniversalSummitStatementInternalUl34

theorem admissibleStandard_non_degenerate : NonDegenerateAdmissible admissibleStandard :=
  ⟨rfl, rfl⟩

/-- Recording the **standard** shape forces canonical shard identities on `d.bundle` (hence non-degeneracy). -/
theorem records_standard_implies_non_degenerate (d : AdmissibleSummitDerivation)
    (hrec : RecordsDependencyShape d dependencyShapeStandard) : NonDegenerateAdmissible d := by
  rcases hrec with ⟨e1, e2, _, _, _, _, _⟩
  exact ⟨e1.symm.trans dependencyShapeStandard_positive_pole, e2.symm.trans dependencyShapeStandard_negative_pole⟩

/-- Standard dual-pole shape is not monopolar. -/
theorem dependencyShapeStandard_not_monopolar : ¬ Monopolar dependencyShapeStandard := by
  simp [Monopolar, HasCanonicalDualPoleShape, dependencyShapeStandard]

/-- Example: negative pole pinned to the canonical internal shard, but positive pole set to `False`
  (so the canonical dual-pole conjunction fails — separation / non-vacuity). -/
def dependencyShapeMonopoleNegative : SummitDependencyShape where
  requiresPositiveCore := False
  requiresNegativeFrontier := icUniversalSummitStatementInternalUl34
  requiresInternalCompletion := icUniversalSummitStatementInternalUl34
  excludesTotalization := icUniversalSummitStatementInternalUl34
  requiresPolarityOrganization := icUniversalSummitStatementInternalUl34

private lemma anatomy_amalg_ne_false : icUniversalSummitStatementAnatomyAmalg ≠ False := by
  intro h
  have ha := ic_summit_anatomy_and_amalgamation_obstruction
  rw [h] at ha
  cases ha

theorem dependencyShapeMonopoleNegative_is_monopolar : Monopolar dependencyShapeMonopoleNegative := by
  simp [Monopolar]
  intro h
  dsimp [HasCanonicalDualPoleShape, dependencyShapeMonopoleNegative] at h
  rcases h with ⟨h1, _⟩
  exact anatomy_amalg_ne_false h1.symm

/-- **T-B6a.1** — Recording + canonical shard content forces **non–monopolar** shape: if the bundle
  carries both canonical shards and `RecordsDependencyShape` holds, the shape cannot be `Monopolar`. -/
theorem not_monopolar_when_records_both_canonical_shards (shape : SummitDependencyShape)
    (d : AdmissibleSummitDerivation) (hrec : RecordsDependencyShape d shape)
    (hpos : d.bundle.anatomyAmalg = icUniversalSummitStatementAnatomyAmalg)
    (hneg : d.bundle.internalUl34 = icUniversalSummitStatementInternalUl34) : ¬ Monopolar shape := by
  intro hm
  rcases hrec with ⟨e1, e2, _, _, _, _, _⟩
  simp [Monopolar, HasCanonicalDualPoleShape, e1, e2, hpos, hneg] at hm

/-- Corollary: standard recording + non-degenerate admissible derivation ⇒ not monopolar. -/
theorem not_monopolar_standard_record_non_degenerate (d : AdmissibleSummitDerivation)
    (hrec : RecordsDependencyShape d dependencyShapeStandard) (hnd : NonDegenerateAdmissible d) :
    ¬ Monopolar dependencyShapeStandard :=
  not_monopolar_when_records_both_canonical_shards dependencyShapeStandard d hrec hnd.1 hnd.2

end InfinityCompression.MetaProof
