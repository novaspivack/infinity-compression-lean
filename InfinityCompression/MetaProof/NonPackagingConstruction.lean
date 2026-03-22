/-
  EPIC_004_PM3 — **Phase 2** (layer 3): provenance predicates + **packaged vs nontrivial** extraction.

  **D-P2.5** — `ConstructedFromArchitectureVia` — ∃ skeleton such that `d` is exactly
  `admissibleFromSkeleton s H`.

  **T-P2.5a** — `crown_eligible_constructs_admissible_via_extraction` — crown eligibility yields a
  constructed admissible record **once** an extraction `H` is fixed.

  **T-P2.6** — `crown_eligible_summit_statement_via_extraction` — same route to
  `icUniversalSummitStatement` **without** invoking `ic_universal_theorem_summit` in the proof.

  **T-P2.7** — `admissibleFrom_skeleton_eq_standard_of_constant_library_extraction` — if `H` ignores
  the skeleton and uses the **library** summit proof terms, the result is **definitionally**
  `admissibleStandard` (`rfl`). At the bare `AdmissibleSummitDerivation` type, **any** `H` already yields
  `admissibleStandard` by proof irrelevance (**T-P3.7** `admissibleFrom_skeleton_eq_admissibleStandard` in
  `LocalToGlobalDerivation.lean`); **T-P2.7** records the **definitional** special case. Distinctness for
  “skeleton-dependent” stories lives in **enriched** / indexed carriers (**T-P3.8**, `SkeletonDependentExtraction`).

  **scope: bookkeeping / interface** — collapse theorem is **not** a negative result about the EPIC;
  it clarifies what remains for a non-packaging breakthrough.
-/

import InfinityCompression.MetaProof.LocalToGlobalDerivation

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-P2.5** — Provenance: `d` arises from skeleton + extraction. -/
def ConstructedFromArchitectureVia {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)
    (d : AdmissibleSummitDerivation) (H : SummitComponentExtraction A) : Prop :=
  ∃ s : ConstructiveDerivationSkeleton A, d = admissibleFromSkeleton s H

/-- Extraction that reuses the **library** summit proof lemmas at every skeleton (constant in `s`). -/
def librarySummitExtraction {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) :
    SummitComponentExtraction A where
  anatomy_amalg := fun _ => ic_summit_anatomy_and_amalgamation_obstruction
  internal_ul34 := fun _ => ic_summit_internal_compression_ul34

/-- **T-P2.5a** — Crown-eligible ⇒ ∃ admissible derivation with provenance via `H`. -/
theorem crown_eligible_constructs_admissible_via_extraction {BD : Type u} {n : Nat}
    (A : CompressionArchitecture BD n) (H : SummitComponentExtraction A) (h : CrownEligible A) :
    ∃ d : AdmissibleSummitDerivation, ConstructedFromArchitectureVia A d H := by
  rcases h.2.1 with ⟨i, j, hij, hp⟩
  let s : ConstructiveDerivationSkeleton A := ⟨i, j, hij, hp⟩
  refine ⟨admissibleFromSkeleton s H, s, rfl⟩

/-- **T-P2.6** — Summit statement along the extraction route (proof avoids `ic_universal_theorem_summit`). -/
theorem crown_eligible_summit_statement_via_extraction {BD : Type u} {n : Nat}
    (A : CompressionArchitecture BD n) (H : SummitComponentExtraction A) (h : CrownEligible A) :
    icUniversalSummitStatement := by
  rcases h.2.1 with ⟨i, j, hij, hp⟩
  let s : ConstructiveDerivationSkeleton A := ⟨i, j, hij, hp⟩
  exact interpret_summit_bundle_standard (interpret_summit_from_skeleton s H)

/-- **T-P2.7** — Constant library extraction collapses to the standard admissible package. -/
theorem admissibleFrom_skeleton_eq_standard_of_constant_library_extraction {BD : Type u} {n : Nat}
    (A : CompressionArchitecture BD n) (s : ConstructiveDerivationSkeleton A) :
    admissibleFromSkeleton s (librarySummitExtraction A) = admissibleStandard := by
  rfl

end InfinityCompression.MetaProof
