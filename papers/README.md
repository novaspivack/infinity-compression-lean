# Papers (`infinity-compression-lean/papers/`)

Shared LaTeX inputs live in **this directory**:

- `suite_preamble.tex` — geometry, fonts, theorem envs, `hyperref`, `cleveref`
- `suite_macros.tex` — suite-wide notation macros

Each paper has its **own subdirectory** and main `.tex` file. From a paper directory, include shared files as:

```latex
\input{../suite_preamble}
\input{../suite_macros}
```

## Layout (series roles)

| Directory | Role |
|-----------|------|
| `Canonical_Certification_and_Enriched_Reflective_Realization/` | **Flagship IC** — internal origin theorem (collapse, split, refinement, fibers) in the native formalization. |
| `External_Validation_Positive_Closure_Architecture/` | **External validation** — transferability across twelve tranches (T1–T12); not the program map. |
| `Fiber_Architecture_Group_Extensions_Lean4/` | **Algebraic / arithmetic engine** — cocycles, splitting, embedding problems, Mathlib bridge. |
| `Quillen_Theorem_A_Galois_Connections/` | **Topology discharge** — Quillen A for Galois connections (nerve / homotopy data). |
| `Mathlib_Cocycle_Splitting_Companion/` | **Mathlib technical note** — reviewer-facing API for the PR; minimal program rhetoric. |
| `Certification_Realization_Obstruction_Universal_Fiber_Architecture/` | **Synthesis** — map of the full program, routes C/A/B/D, cross-domain dictionary. |
| `Reflective_Non_Exhaustion_Summit/` | **Summit** — distilled reflective non-exhaustion thesis, scope, Gödel distinction. |

## Build (example)

```bash
cd papers/Canonical_Certification_and_Enriched_Reflective_Realization
latexmk -pdf Canonical_Certification_and_Enriched_Reflective_Realization.tex
```

Normative paper program: `specs/COMPLETE/EPIC_016_WV2_PROGRAM_W_PAPERS_SPEC.md` (parent repo).
