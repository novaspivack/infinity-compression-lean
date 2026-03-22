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

Both sides equal `σ(g₁)·σ(g₂)·σ(g₃)·σ(g₁g₂g₃)⁻¹` after cancellation of
intermediate section values. The proof uses `section_mul_eq` to expand and cancel.
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
  -- Both sides = σ(g₁)*σ(g₂)*σ(g₃)*σ(g₁g₂g₃)⁻¹ after cancellation.
  -- LHS cancels σ(g₁g₂)⁻¹ * σ(g₁g₂) and σ(g₁g₂g₃)⁻¹ * σ(g₁g₂g₃)⁻¹.
  -- RHS cancels σ(g₁)⁻¹ * σ(g₁) and σ(g₂g₃)⁻¹ * σ(g₂g₃).
  -- Both are straightforward group-theoretic cancellations in E.
  -- We extract the common value by right-multiplying by σ(g₁g₂g₃).
  have key : ∀ (x : E),
    x * σ.toFun (g₁ * g₂ * g₃) = σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ →
    x = σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ * (σ.toFun (g₁ * g₂ * g₃))⁻¹ := by
    intro x hx; rw [← hx, mul_assoc, mul_inv_cancel, mul_one]
  have lhs_cancel : (σ.toFun (g₁ * g₂) * σ.toFun g₃ * (σ.toFun (g₁ * g₂ * g₃))⁻¹ *
    (σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹)) * σ.toFun (g₁ * g₂ * g₃) =
    σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ := by
    have h12 := section_mul_eq S σ g₁ g₂
    have h123 := section_mul_eq S σ (g₁ * g₂) g₃
    -- σ(g₁)*σ(g₂) = inl(c12)*σ(g₁g₂), so σ(g₁)*σ(g₂)*σ(g₁g₂)⁻¹ = inl(c12)
    -- σ(g₁g₂)*σ(g₃) = inl(c123)*σ(g₁g₂g₃)
    -- LHS*σ(g₁g₂g₃) = inl(c123)*σ(g₁g₂g₃)*σ(g₁g₂g₃)⁻¹*inl(c12)*σ(g₁g₂g₃)
    --                 = inl(c123)*inl(c12)*σ(g₁g₂g₃) ... no, let me just compute directly
    calc (σ.toFun (g₁ * g₂) * σ.toFun g₃ * (σ.toFun (g₁ * g₂ * g₃))⁻¹ *
           (σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹)) * σ.toFun (g₁ * g₂ * g₃)
        = σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹ *
          (σ.toFun (g₁ * g₂) * σ.toFun g₃ * (σ.toFun (g₁ * g₂ * g₃))⁻¹ *
           σ.toFun (g₁ * g₂ * g₃)) := by
          rw [mul_comm (σ.toFun (g₁ * g₂) * σ.toFun g₃ * (σ.toFun (g₁ * g₂ * g₃))⁻¹)
                       (σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹)]
          rw [mul_assoc]
      _ = σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹ *
          (σ.toFun (g₁ * g₂) * σ.toFun g₃) := by
          congr 1
          rw [mul_assoc, inv_mul_cancel_left]
      _ = σ.toFun g₁ * σ.toFun g₂ * ((σ.toFun (g₁ * g₂))⁻¹ * (σ.toFun (g₁ * g₂) * σ.toFun g₃)) := by
          rw [mul_assoc]
      _ = σ.toFun g₁ * σ.toFun g₂ * ((σ.toFun (g₁ * g₂))⁻¹ * σ.toFun (g₁ * g₂) * σ.toFun g₃) := by
          rw [mul_assoc (σ.toFun (g₁ * g₂))⁻¹]
      _ = σ.toFun g₁ * σ.toFun g₂ * (1 * σ.toFun g₃) := by
          rw [inv_mul_cancel]
      _ = σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ := by
          rw [one_mul]
  have rhs_cancel : (σ.toFun g₁ * (σ.toFun g₂ * σ.toFun g₃ * (σ.toFun (g₂ * g₃))⁻¹) *
    (σ.toFun g₁)⁻¹ *
    (σ.toFun g₁ * σ.toFun (g₂ * g₃) * (σ.toFun (g₁ * g₂ * g₃))⁻¹)) * σ.toFun (g₁ * g₂ * g₃) =
    σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ := by
    calc (σ.toFun g₁ * (σ.toFun g₂ * σ.toFun g₃ * (σ.toFun (g₂ * g₃))⁻¹) *
           (σ.toFun g₁)⁻¹ *
           (σ.toFun g₁ * σ.toFun (g₂ * g₃) * (σ.toFun (g₁ * g₂ * g₃))⁻¹)) *
           σ.toFun (g₁ * g₂ * g₃)
        = σ.toFun g₁ * (σ.toFun g₂ * σ.toFun g₃ * (σ.toFun (g₂ * g₃))⁻¹) *
          (σ.toFun g₁)⁻¹ *
          (σ.toFun g₁ * σ.toFun (g₂ * g₃)) := by
          rw [mul_assoc _ (σ.toFun (g₁ * g₂ * g₃))⁻¹, inv_mul_cancel_left]
          rw [mul_assoc]
      _ = σ.toFun g₁ * (σ.toFun g₂ * σ.toFun g₃ * (σ.toFun (g₂ * g₃))⁻¹) *
          ((σ.toFun g₁)⁻¹ * (σ.toFun g₁ * σ.toFun (g₂ * g₃))) := by
          rw [mul_assoc]
      _ = σ.toFun g₁ * (σ.toFun g₂ * σ.toFun g₃ * (σ.toFun (g₂ * g₃))⁻¹) *
          σ.toFun (g₂ * g₃) := by
          rw [inv_mul_cancel_left]
      _ = σ.toFun g₁ * (σ.toFun g₂ * σ.toFun g₃ * ((σ.toFun (g₂ * g₃))⁻¹ * σ.toFun (g₂ * g₃))) := by
          rw [mul_assoc, mul_assoc (σ.toFun g₂ * σ.toFun g₃)]
      _ = σ.toFun g₁ * (σ.toFun g₂ * σ.toFun g₃) := by
          rw [inv_mul_cancel, mul_one]
      _ = σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ := by
          rw [mul_assoc]
  exact (key _ lhs_cancel).symm.trans (key _ rhs_cancel)

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
