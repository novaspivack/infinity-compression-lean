# infinity-compression-lean — Artifact companion

**Role:** Citation-facing companion to `MANIFEST.md` and `README.md` for the Infinity Compression Lean library.

## What this artifact is

Lean 4 formalization of the **Infinity Compression** program (EPIC_001). Root import: `InfinityCompression.lean`. Papers live under `papers/`; Program W external-validation benchmarks live under `InfinityCompression/Validation/`.

## Authoritative inventories

| Document | Contents |
|----------|----------|
| `MANIFEST.md` | Full `.lean` inventory, EPIC mapping, Sorry status, Program W **T1–T12** validation modules |
| `README.md` | Build instructions, release checklist, key summit theorems |

## Program W — external validation (specs + LaTeX)

- **Consolidated paper:** `papers/External_Validation_Positive_Closure_Architecture/External_Validation_Positive_Closure_Architecture.tex` (**T1–T12**).
- **Specs:** `EPIC_015_WV1` (T1), `EPIC_016_WV2` (T2–T3), `EPIC_017_EV1` (T4–T7), `EPIC_018_XC1` (T8–T12) — paths under `specs/COMPLETE/` in the outer `infinity-compression` repo.
- **Verdict / methodology notes:** `specs/NOTES/Program_W_Validation_Verdict.md`, `specs/NOTES/EPIC_THEOREM_INVENTORY_LEAN_PAPER_PREP.md` (outer repo).

## Reproducibility

Pin Lean and Mathlib via `lean-toolchain`, `lakefile.lean`, and **`lake-manifest.json`** — commit them with substantive changes so collaborators resolve identical dependencies.

## Archive / DOI

No Zenodo (or other) identifier is assigned from this workspace; add a row here when a versioned release is published.
