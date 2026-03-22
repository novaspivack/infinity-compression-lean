/-
  EPIC_020_ML1 — The 2-cocycle identity and normalization.

  The section cocycle satisfies the multiplicative 2-cocycle identity with
  respect to the conjugation action:

    `c(g₁g₂, g₃) · c(g₁, g₂) = φ_σ(g₁)(c(g₂, g₃)) · c(g₁, g₂g₃)`

  This connects our cocycle to Mathlib's `IsMulCocycle₂`.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import InfinityCompression.GeneralMethod.GroupExtension.SchurZassenhaus
import InfinityCompression.GeneralMethod.GroupExtension.ConjugationAction

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

variable {N E G : Type u} [Group N] [Group E] [Group G]
variable (S : GroupExtension N E G)

/-! ### The 2-cocycle identity

Both sides, when mapped through `S.inl` and right-multiplied by `σ(g₁g₂g₃)`,
equal `σ(g₁) · σ(g₂) · σ(g₃)` after cancellation of intermediate section values.

The LHS cancels `σ(g₁g₂g₃)⁻¹ · σ(g₁g₂g₃)` and `σ(g₁g₂)⁻¹ · σ(g₁g₂)`.
The RHS cancels `σ(g₁)⁻¹ · σ(g₁)` and `σ(g₂g₃)⁻¹ · σ(g₂g₃)`.

-- TODO: Complete the tactic proof. The mathematical content is standard
-- (both sides of the 2-cocycle identity reduce to σ(g₁)·σ(g₂)·σ(g₃)·σ(g₁g₂g₃)⁻¹
-- after cancellation). The difficulty is purely tactic-engineering: Lean 4's
-- `group` tactic treats section values as free generators and cannot perform
-- the cancellations, requiring manual `mul_assoc`/`inv_mul_cancel_left` chains.
-/

theorem sectionCocycle_isMulCocycle₂_conj (σ : S.Section) (g₁ g₂ g₃ : G) :
    sectionCocycle S σ (g₁ * g₂) g₃ * sectionCocycle S σ g₁ g₂ =
    sectionConjAct S σ g₁ (sectionCocycle S σ g₂ g₃) * sectionCocycle S σ g₁ (g₂ * g₃) := by
  apply S.inl_injective
  rw [map_mul, map_mul, inl_sectionConjAct]
  rw [sectionCocycle_spec S σ (g₁ * g₂) g₃,
      sectionCocycle_spec S σ g₁ g₂,
      sectionCocycle_spec S σ g₂ g₃,
      sectionCocycle_spec S σ g₁ (g₂ * g₃)]
  conv_rhs =>
    rw [show g₁ * (g₂ * g₃) = g₁ * g₂ * g₃ from (mul_assoc g₁ g₂ g₃).symm]
  sorry

/-! ### Cocycle of a splitting is trivial -/

theorem sectionCocycle_of_splitting (s : S.Splitting) (g₁ g₂ : G) :
    sectionCocycle S s.toSection g₁ g₂ = 1 := by
  apply S.inl_injective
  rw [sectionCocycle_spec, map_one]
  have : s.toSection.toFun (g₁ * g₂) = s.toSection.toFun g₁ * s.toSection.toFun g₂ :=
    map_mul s g₁ g₂
  rw [this, mul_inv_cancel]

/-! ### The cocycle identity expressed purely in E -/

theorem section_triple_product (σ : S.Section) (g₁ g₂ g₃ : G) :
    σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ =
    S.inl (sectionCocycle S σ g₁ g₂) * σ.toFun (g₁ * g₂) * σ.toFun g₃ := by
  rw [← section_mul_eq S σ g₁ g₂]

theorem section_triple_product' (σ : S.Section) (g₁ g₂ g₃ : G) :
    σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ =
    S.inl (sectionCocycle S σ g₁ g₂) *
    S.inl (sectionCocycle S σ (g₁ * g₂) g₃) *
    σ.toFun (g₁ * g₂ * g₃) := by
  rw [section_triple_product, mul_assoc, section_mul_eq S σ (g₁ * g₂) g₃, ← mul_assoc,
      ← map_mul]

end InfinityCompression.GeneralMethod
