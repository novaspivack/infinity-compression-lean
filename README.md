# infinity-compression-lean

Lean 4 formalization of the **Infinity Compression** program. Root import: `InfinityCompression.lean`.

## What it proves

The central result is that **canonical certification does not exhaust reflective structure**: when a formal system has a bare certification layer and a richer realization layer, the two cannot be collapsed. The difference is organized by fibers, sections, and obstruction laws. The summit theorem (`ic_universal_theorem_summit`) is a unified fixed-point result connecting the internal collapse barrier to the external realization gap.

The program also includes:
- **External validation** across twelve mathematical families (T1–T12 benchmark suite)
- **Algebraic discharge**: group extensions, section cocycles, splitting criterion, cohomological bridge for Mathlib
- **Topological discharge**: Quillen's Theorem A for Galois connections (first machine-checked formalization)
- **Computability anchors**: halting and Rice self-certification

## Build

```bash
lake update
lake exe cache get   # pre-built Mathlib .olean files (strongly recommended)
lake build
```

**Policy:** Zero `sorry` in proof terms; standard Mathlib + Lean kernel axioms only.

## Key theorems

| Name | File | Description |
|------|------|-------------|
| `ic_universal_theorem_summit` | `Frontier/ICUniversalTheorem.lean` | Central summit: canonical certification ≠ enriched realization |
| `ic_universal_theorem_landscape` | same | Maximal aggregation |
| `ic_universal_theorem_summit_iff_components` | same | Summit ↔ two named component shards |
| `reflexive_architecture_necessity` | `Frontier/ReflexiveArchitectureNecessity.lean` | Canonical spine necessity |
| `summit_and_spine_necessity_joint` | `Frontier/SummitDerivation.lean` | Joint derivation |
| `ul3_no_final_positive_compressor_ic_abstract` | `Frontier/ICAntiTranslation.lean` | Anti-translation barrier |
| `crown_eligible_pin_structural_mirror` | `MetaProof/NonPackagingCorrespondence.lean` | Mirror witness |
| `nems_meta_summit_provenance_nontrivial` | `MetaProof/MetaSummitProvenance.lean` | Provenance nontriviality |

See [MANIFEST.md](MANIFEST.md) for the complete theorem inventory.

## Papers

This library accompanies a series of papers published on Zenodo:
- Canonical Certification Does Not Exhaust Reflective Structure (flagship)
- External Validation of a Positive-Closure Proof Architecture
- Fiber Architecture for Group Extensions in Lean 4
- Completing the Cohomological Extension Package (Mathlib companion)
- Quillen's Theorem A for Galois Connections
- Certification, Realization, and Obstruction: A Universal Fiber Architecture
- Reflective Non-Exhaustion Summit

See [novaspivack.com/research](https://www.novaspivack.com/research) for DOI links.

## Toolchain

`lean-toolchain` and `lakefile.lean` pin Lean 4 and Mathlib versions. See [ARTIFACT.md](ARTIFACT.md) for the exact fingerprint.
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429241
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
<!-- NOVA_ZPO_ZENODO_PAPER_BEGIN -->
**Archival paper (Zenodo preprint) (Zenodo):** https://doi.org/10.5281/zenodo.19430501
<!-- NOVA_ZPO_ZENODO_PAPER_END -->
