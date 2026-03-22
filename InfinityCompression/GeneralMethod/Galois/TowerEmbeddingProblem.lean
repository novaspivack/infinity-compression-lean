/-
  EPIC_GS1 Milestone 1 (completion) — **bundled** Galois tower embedding problem.

  For `M : IntermediateField K L` with `K` normal in both `M` and `L`, Mathlib’s
  `AlgEquiv.restrictNormalHom M` is a surjective homomorphism `Gal(L/K) ↠ Gal(M/K)`.
  This packages the abstract `EmbeddingProblem` from `EmbeddingProblem.lean` on **actual**
  Galois groups (no elaboration-only pattern).

  **Lean note:** Mathlib requires `set_option backward.isDefEq.respectTransparency false` and
  `open scoped Pointwise` to elaborate `restrictNormalHom` on `IntermediateField` (see
  `IntermediateField.restrictNormalHom_ker` in `FieldTheory.Galois.Basic`).

  **Reference:** `Mathlib.FieldTheory.Normal.Defs` (`AlgEquiv.restrictNormalHom`),
  `Mathlib.FieldTheory.Normal.Basic` (`AlgEquiv.restrictNormalHom_surjective`).
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Normal.Basic

import InfinityCompression.GeneralMethod.Galois.EmbeddingProblem

namespace InfinityCompression.GeneralMethod.Galois

open GroupExtension

open IntermediateField AlgEquiv

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

set_option backward.isDefEq.respectTransparency false in
/-- Galois tower restriction as an abstract embedding problem: `Gal(L/K) ↠ Gal(M/K)`.

  Use `M` for the intermediate field to avoid clashing with the carrier in `Gal(M/K)` notation.

  **Instances:** `IntermediateField` supplies `Algebra (↥M) L` and `IsScalarTower K (↥M) L`
  (`IntermediateField.isScalarTower_mid'`). -/
noncomputable def towerEmbeddingProblem (M : IntermediateField K L) [Normal K M] [Normal K L] :
    EmbeddingProblem (Gal(M/K)) (Gal(L/K)) where
  surjection := restrictNormalHom M
  surjective := by
    apply restrictNormalHom_surjective

theorem towerEmbeddingProblem_solvable_iff_trivial_cocycle (M : IntermediateField K L)
    [Normal K M] [Normal K L] :
    Nonempty (towerEmbeddingProblem M).Solution ↔
      ∃ σ : (towerEmbeddingProblem M).toGroupExtension.Section,
        ∀ g₁ g₂ : Gal(M/K),
          sectionCocycle (towerEmbeddingProblem M).toGroupExtension σ g₁ g₂ = 1 :=
  EmbeddingProblem.solvable_iff_trivial_cocycle (towerEmbeddingProblem M)

end InfinityCompression.GeneralMethod.Galois
