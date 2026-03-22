# infinity-compression-lean

Lean 4 formalization of the **Infinity Compression** program (EPIC_001). Root import: `InfinityCompression.lean`.

## Build

```bash
lake build
```

**Policy:** zero `sorry` in proof terms under `InfinityCompression/`; standard Mathlib + Lean kernel axioms only.

## Release / audit (freeze checklist)

- **Build:** `lake build` succeeds.
- **Manifest:** `MANIFEST.md` — full module inventory, EPIC mapping, open `def`s, summit/landscape theorems.
- **Crown reader:** `../specs/NOTES/Crown_Summit_Reader.md`
- **Closed vs open:** `../specs/NOTES/IC_Closed_Open_Ledger.md`
- **Route B roadmap (prose):** `../specs/NOTES/Summit_B.md`
- **Program spec:** `../specs/IN-PROCESS/EPIC_001_X7R_INFINITY_COMPRESSION_PROGRAM_SPEC.md` (§6.1 implementation status)
- **EPIC_006_CN1 (crown → nonaccidental summit):** `../specs/IN-PROCESS/EPIC_006_CN1_CROWN_NECESSITY_IRREDUCIBILITY_NONACCIDENTAL_SUMMIT_SPEC.md` — Program **E** (`ProgramECrownSummit.lean`); **006E** (`ProgramE006EReflectiveFixedPoint.lean`, **D-E6.5**, **T-E6.5**–**T-E6.8**). **Epistemology:** **T-B7.1** / **T-B9.1** / mirror lemmas still use **`ic_universal_theorem_summit`** for the library standard derivation — see `IC_Closed_Open_Ledger.md` and EPIC **§7.5**.
- **EPIC_007_AS1 (post-summit — autonomous mirror):** `../specs/IN-PROCESS/EPIC_007_AS1_SUMMIT_INDEPENDENT_REFLECTIVE_MIRROR_SPEC.md` — **Lean v0:** `MetaProof/ReflectiveMirrorWitness.lean`, `MetaProof/AutonomousMirrorConstruction.lean` (**T-F1.1a**–**T-F1.5**). Full summit-independence of the **derivation** witness from **T-P2.7** remains **open** (needs skeleton-dependent extraction).

## Key summit theorems

| Name | File |
|------|------|
| `ic_universal_theorem_summit` | `Frontier/ICUniversalTheorem.lean` |
| `ic_universal_theorem_landscape` | same (maximal aggregation) |
| `ic_universal_theorem_summit_iff_components` | same (S3: summit ↔ two named shards) |
| `reflexive_architecture_necessity` | `Frontier/ReflexiveArchitectureNecessity.lean` (S1: canonical spine) |
| `summit_and_spine_necessity_joint`, `crown_eligible_implies_summit_statement` | `Frontier/SummitDerivation.lean` (S2; see module doc) |
| `summit_bundle_matches_ic_universal_summit`, `standard_shape_matches_summit_iff`, `summit_requires_dual_poles` | `MetaProof/*` (EPIC_002_BH2 Route B) |
| `crown_eligible_induces_mirror`, `dependencyShapeStandard_minimal`, `reflexive_meta_crown`, … | `MetaProof/*` (EPIC_003_BH6 Route B continuation; see `MANIFEST.md`) |
| `crown_eligible_pin_structural_mirror` (**T-P1.1**) | `MetaProof/NonPackagingCorrespondence.lean` (EPIC_004_PM3 Phase 1) |
| `crown_eligible_nonempty_skeleton` (**T-P2.1**), `crown_eligible_summit_statement_via_extraction` (**T-P2.6**), collapse audit (**T-P2.7**), proof-irrelevance barrier (**T-P3.7**) | `MetaProof/ConstructiveDerivationSkeleton.lean`, `LocalToGlobalDerivation.lean`, `NonPackagingConstruction.lean` (EPIC_004_PM3 Phase 2; **T-P3.7** EPIC_005) |
| `nems_meta_summit_provenance_nontrivial` (**T-P3.3**), role skeletons (**T-P3.1**–**T-P3.2d**), bridge (**T-P3.5**–**T-P3.6**), enriched tag (**T-P3.8**) | `MetaProof/RoleSeparatedSkeleton.lean`, `MetaProof/MetaSummitProvenance.lean`, `MetaProof/SkeletonIndexedExtractionBridge.lean`, `MetaProof/EnrichedAdmissibleSummitDerivation.lean` (EPIC_005_RK7) |
| `ul3_no_final_positive_compressor_ic_abstract`, `ul4_internal_compression_without_totalization_ic_abstract` | `Frontier/ICAntiTranslation.lean` |
| Program **E** (**D-E6.1**, **T-E6.1**–**T-E6.4**), `records_standard_implies_non_degenerate` | `MetaProof/ProgramECrownSummit.lean`, `MetaProof/DerivationNecessity.lean` (EPIC_006_CN1) |
| **006E** reflective fixed-point (**D-E6.5**, **T-E6.5**–**T-E6.8**) | `MetaProof/ProgramE006EReflectiveFixedPoint.lean` (EPIC_006_CN1) |
| EPIC_007_AS1 **T-F1** family (**D-F1.1**–**D-F1.3**) | `MetaProof/ReflectiveMirrorWitness.lean`, `MetaProof/AutonomousMirrorConstruction.lean` |

## Toolchain

`lean-toolchain` and `lakefile.lean` pin Lean 4 and Mathlib versions.
