/-
  EPIC_GS1 Milestone 1 — Arithmetic bridge (Galois towers ↔ embedding problems).

  **Mathematical content (Milestone 1 of EPIC_GS1):**

  For a tower `L / E / K` of fields with `E : IntermediateField K L` and `E/K`, `L/K` normal,
  restriction of automorphisms yields a surjective group homomorphism
  `Gal(L/K) ↠ Gal(E/K)` (Mathlib: `AlgEquiv.restrictNormalHom`). Its kernel is the fixing
  subgroup `E.fixingSubgroup` (identified with `Gal(L/E)`), proved as
  `IntermediateField.restrictNormalHom_ker`.

  Together with `InfinityCompression.GeneralMethod.Galois.EmbeddingProblem`, this is the
  **field-theoretic** discharge: the abstract `EmbeddingProblem` / cocycle story applies to
  *actual* Galois groups once one packages `φ = restrictNormalHom E`. Mathlib already proves
  surjectivity (`AlgEquiv.restrictNormalHom_surjective`).

  **Lean note:** Bundling `EmbeddingProblem (Gal(E/K)) (Gal(L/K))` in one definition can hit
  elaboration friction around `Gal` and `IntermediateField` coercions; use
  `EmbeddingProblem.mk` with `φ := AlgEquiv.restrictNormalHom E` and
  `AlgEquiv.restrictNormalHom_surjective` in contexts where instances are available, or invoke
  the abstract theorems (`solvable_iff_splits`, `solvable_iff_trivial_cocycle`) on a
  manually constructed `EmbeddingProblem`.

  **Reference:** `FieldTheory.Galois.Basic`, `FieldTheory.Normal.Basic`.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic

import InfinityCompression.GeneralMethod.Galois.EmbeddingProblem

universe u

namespace InfinityCompression.GeneralMethod.Galois

open IntermediateField

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-! ### Re-exports (Mathlib Galois tower theorems) -/

/-- Restriction `Gal(L/K) →* Gal(E/K)` is surjective when `E/K` and `L/K` are normal. -/
alias galois_restrictNormalHom_surjective := AlgEquiv.restrictNormalHom_surjective

/-- Kernel of restriction is the fixing subgroup of `E` (`Gal(L/E)` in the finite Galois case). -/
alias galois_restrictNormalHom_ker := IntermediateField.restrictNormalHom_ker

/-! ### Non-bundled packaging pattern

To obtain an `EmbeddingProblem (Gal(E/K)) (Gal(L/K))` from a normal intermediate field `E`, use:

`EmbeddingProblem.mk (AlgEquiv.restrictNormalHom E) (AlgEquiv.restrictNormalHom_surjective)`

when Lean can synthesize the tower instances (in particular `Algebra` data for `↥E` over `L`).
Then `EmbeddingProblem.solvable_iff_splits` and `EmbeddingProblem.solvable_iff_trivial_cocycle`
apply verbatim.
-/

end InfinityCompression.GeneralMethod.Galois
