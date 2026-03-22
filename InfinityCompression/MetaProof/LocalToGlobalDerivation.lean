/-
  EPIC_004_PM3 — **Phase 2** (layer 2): **local → global** summit derivation, **conditional** on an
  explicit extraction interface.

  **D-P2.3** — `SummitComponentExtraction` bundles the *hypotheses* that each summit shard can be
  justified from **any** skeleton on `A`. This keeps `AdmissibleSummitDerivation` itself slim
  (per advisor: no junk fields on the certified record).

  **T-P2.3** / **T-P2.4** — Skeleton + extraction ⇒ admissible derivation + well-formedness, without
  mentioning `admissibleStandard` in the *statement* of the construction function.

  **scope: interface** — a **constant** extraction (ignoring the skeleton) recovers the library
  summit lemmas and is **definitionally** `admissibleStandard` (see `NonPackagingConstruction.lean`).

  **T-P3.7** — `admissibleFrom_skeleton_eq_irrespective_of_skeleton`: along `admissibleFromSkeleton`, the
  **`AdmissibleSummitDerivation`** value is **skeleton-independent** for **any** `SummitComponentExtraction`
  (proof irrelevance on the two `Prop` witnesses). So “strong in-record” inequality at **this** type
  cannot come from varying `H` or `s` alone — see `EPIC_005_RK7` **§6.3** / **§8.5**.

  **EPIC_007_AS1** — `records_dependency_shape_admissibleFromSkeleton`: standard **recording** for any
  `admissibleFromSkeleton` package (used by `ReflectiveMirrorWitness`).
-/

import InfinityCompression.MetaProof.AdmissibleDerivations
import InfinityCompression.MetaProof.ConstructiveDerivationSkeleton

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-P2.3** — Hypothesis family: from any skeleton on `A`, produce witnesses for the two named
  §2.5 shard propositions. -/
structure SummitComponentExtraction {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) :
    Type where
  anatomy_amalg :
    ∀ _s : ConstructiveDerivationSkeleton A, icUniversalSummitStatementAnatomyAmalg
  internal_ul34 :
    ∀ _s : ConstructiveDerivationSkeleton A, icUniversalSummitStatementInternalUl34

/-- **D-P2.4** — Certified admissible record built from a skeleton + extraction (no `admissibleStandard`
  in this definition). -/
def admissibleFromSkeleton {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) : AdmissibleSummitDerivation :=
  { bundle := summitBundleStandard
    anatomyWitness := H.anatomy_amalg s
    internalWitness := H.internal_ul34 s }

/-- **T-P2.3** — Well-formedness of `admissibleFromSkeleton` from extraction hypotheses alone. -/
theorem wellFormed_admissibleFromSkeleton {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) :
    WellFormedAdmissible (admissibleFromSkeleton s H) :=
  ⟨H.anatomy_amalg s, H.internal_ul34 s⟩

/-- **T-P2.4** — Standard bundle interpretation from extraction (still no `ic_universal_theorem_summit`
  in this lemma’s proof). -/
theorem interpret_summit_from_skeleton {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) :
    interpretSummitBundle (admissibleFromSkeleton s H).bundle :=
  ⟨H.anatomy_amalg s, H.internal_ul34 s⟩

/-- **T-P3.7** (universal collapse) — Along `admissibleFromSkeleton` with `summitBundleStandard`, the two
  witness fields are proofs of **fixed** `Prop`s. By **proof irrelevance**, the resulting
  `AdmissibleSummitDerivation` is **exactly** the library packaging `admissibleStandard`, for **every**
  skeleton and **every** `SummitComponentExtraction` `H`.

  **Consequence:** **T-P2.7** is not special to `librarySummitExtraction` at the `AdmissibleSummitDerivation`
  type — any Phase-2 extraction path with the standard bundle collapses to the same bare record. “Strong
  in-record non-collapse” requires **enrichment** (**T-P3.8**), a **non-standard** `SummitBundle`, or
  tracking distinction outside this `Prop`-only surrogate. -/
theorem admissibleFrom_skeleton_eq_admissibleStandard {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) :
    admissibleFromSkeleton s H = admissibleStandard := by
  simp [admissibleFromSkeleton, admissibleStandard]

/-- **T-P3.7** — Skeleton independence for fixed `H`, as a corollary of **universal collapse** to
  `admissibleStandard`. -/
theorem admissibleFrom_skeleton_eq_irrespective_of_skeleton {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (s₁ s₂ : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) :
    admissibleFromSkeleton s₁ H = admissibleFromSkeleton s₂ H :=
  (admissibleFrom_skeleton_eq_admissibleStandard s₁ H).trans (admissibleFrom_skeleton_eq_admissibleStandard s₂ H).symm

/-- Any `admissibleFromSkeleton` package (standard bundle) **records** the standard dependency shape. -/
theorem records_dependency_shape_admissibleFromSkeleton {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (s : ConstructiveDerivationSkeleton A) (H : SummitComponentExtraction A) :
    RecordsDependencyShape (admissibleFromSkeleton s H) dependencyShapeStandard := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rfl
  · exact H.anatomy_amalg s
  · exact H.internal_ul34 s

end InfinityCompression.MetaProof
