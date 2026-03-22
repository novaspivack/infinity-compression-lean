# Papers (`infinity-compression-lean/papers/`)

Shared LaTeX inputs live in **this directory**:

- `suite_preamble.tex` — geometry, fonts, theorem envs, `hyperref`, `cleveref`
- `suite_macros.tex` — suite-wide notation macros

Each paper has its **own subdirectory** and main `.tex` file. From a paper directory, include shared files as:

```latex
\input{../suite_preamble}
\input{../suite_macros}
```

## Layout

| Directory | Paper |
|-----------|--------|
| `Canonical_Certification_and_Enriched_Reflective_Realization/` | Flagship IC paper (canonical bare certification vs enriched realization; fibers; NEMS spine). |
| `Program_W_External_Validation/` | Program W methods / external validation benchmark (quotient / fiber / section). **In progress.** |

## Build (example)

```bash
cd papers/Canonical_Certification_and_Enriched_Reflective_Realization
latexmk -pdf Canonical_Certification_and_Enriched_Reflective_Realization.tex
```

Normative paper program specs: `specs/IN-PROCESS/EPIC_016_WV2_PROGRAM_W_PAPERS_SPEC.md` (parent repo).
