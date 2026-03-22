# infinity-compression-lean — Artifact companion

**Role:** Citation-facing companion to `MANIFEST.md` and `README.md` for the Infinity Compression Lean library.

## What this artifact is

Lean 4 formalization of the **Infinity Compression** program (EPIC_001) and the **General Method** program (EPICs 019–022). Root import: `InfinityCompression.lean`. Papers live under `papers/`; external-validation benchmarks under `InfinityCompression/Validation/`; general-method modules under `InfinityCompression/GeneralMethod/`.

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
