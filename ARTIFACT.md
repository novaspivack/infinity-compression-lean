# infinity-compression-lean — Artifact companion

**Role:** Citation-facing companion to `MANIFEST.md` and `README.md` for the Infinity Compression Lean library.

## What this artifact is

Lean 4 formalization of the **Infinity Compression** program (EPIC_001) and the **General Method** program (EPICs 019–022). Root import: `InfinityCompression.lean`. Papers live under `papers/`; external-validation benchmarks under `InfinityCompression/Validation/`; general-method modules under `InfinityCompression/GeneralMethod/`. The **Gödel-scale summit program** (EPIC_GS1) is tracked in `specs/IN-PROCESS/EPIC_GS1_GODEL_SCALE_SUMMIT_PROGRAM_SPEC.md`. **Lean:** Milestone 1 — `GeneralMethod/Galois/GaloisEmbeddingBridge.lean`; Milestone 2 (Route D) — `GeneralMethod/RouteD/SelfCertificationHalting.lean`; Milestones 4–6 — `GeneralMethod/Summit/ReflectiveNonExhaustion.lean`; Milestone 5 dictionary hub — `GeneralMethod/Summit/CrossDomainDictionary.lean`. **Prose (Milestone 3 draft):** `specs/IN-PROCESS/EPIC_GS1_M3_MANIFESTO_SYNTHESIS_DRAFT.md`.

## Authoritative inventories

| Document | Contents |
|----------|----------|
| `MANIFEST.md` | Full `.lean` inventory, EPIC mapping, sorry status, all module tables |
| `README.md` | Build instructions, release checklist, key summit theorems |

## Key theorem-level results (zero sorry)

| Theorem | Module | Significance |
|---------|--------|-------------|
| `splits_iff_trivial_cocycle` | `GroupExtension/SchurZassenhaus.lean` | Extension splits iff cocycle trivial; fills Mathlib TODO |
| `solvable_iff_trivial_cocycle` | `Galois/EmbeddingProblem.lean` | Embedding problem solvable iff cocycle vanishes |
| `quillenA` | `Quillen/QuillenTheoremA.lean` | Quillen's Theorem A for Galois connections |
| `nerve_connected_to_terminal` | `Quillen/NerveContractibility.lean` | Nerve contractibility for terminal categories |
| `routeD_certification_cannot_equal_halting_realization` | `RouteD/SelfCertificationHalting.lean` | EPIC_GS1 Route D: halting not a computable predicate on codes (Mathlib halting problem) |
| `reflective_non_exhaustion_existential` | `Summit/ReflectiveNonExhaustion.lean` | EPIC_GS1: from any `ReflectiveCertificationArchitecture`, two realizations share a bare certificate |
| `crossDomain_dictionary_imports_ok` | `Summit/CrossDomainDictionary.lean` | EPIC_GS1 Milestone 5: single import hub for five discharge stacks |

## Papers (5-paper series)

| Paper | Directory | Focus |
|-------|-----------|-------|
| IC flagship | `Canonical_Certification_and_Enriched_Reflective_Realization/` | Internal architecture theorem |
| External validation | `External_Validation_Positive_Closure_Architecture/` | 12-tranche transferability survey |
| ITP/CPP | `Fiber_Architecture_Group_Extensions_Lean4/` | Group extensions, cocycles, embedding problems |
| Mathlib companion | `Mathlib_Cocycle_Splitting_Companion/` | Upstream PR technical note |
| Quillen Theorem A | `Quillen_Theorem_A_Galois_Connections/` | Homotopy equivalence for Galois connections |

## Reproducibility

Pin Lean and Mathlib via `lean-toolchain` (`leanprover/lean4:v4.29.0-rc6`), `lakefile.lean`, and **`lake-manifest.json`** — commit them with substantive changes so collaborators resolve identical dependencies.

## Archive / DOI

No Zenodo (or other) identifier is assigned from this workspace; add a row here when a versioned release is published.
