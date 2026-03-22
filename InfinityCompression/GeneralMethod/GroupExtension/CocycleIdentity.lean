/-
  EPIC_020_ML1 — The 2-cocycle identity and normalization.

  The section cocycle satisfies the multiplicative 2-cocycle identity with
  respect to the conjugation action:

    `c(g₁, g₂) · c(g₁g₂, g₃) = φ_σ(g₁)(c(g₂, g₃)) · c(g₁, g₂g₃)`

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

The associativity of the triple product `σ(g₁) * σ(g₂) * σ(g₃)` computed
two ways yields the cocycle identity. Way 1 (left-associated) gives
`inl(c₁₂) * inl(c₁₂₃) * σ₁₂₃`, and Way 2 (right-associated with
conjugation) gives `inl(φ(g₁)(c₂₃)) * inl(c₁_₂₃) * σ₁₂₃`. Cancelling
`σ₁₂₃` and applying `inl_injective` gives the identity.
-/

theorem sectionCocycle_isMulCocycle₂_conj (σ : S.Section) (g₁ g₂ g₃ : G) :
    sectionCocycle S σ g₁ g₂ * sectionCocycle S σ (g₁ * g₂) g₃ =
    sectionConjAct S σ g₁ (sectionCocycle S σ g₂ g₃) * sectionCocycle S σ g₁ (g₂ * g₃) := by
  apply S.inl_injective
  rw [map_mul, map_mul, inl_sectionConjAct]
  -- Goal: inl(c₁₂)*inl(c₁₂₃) = σ₁*inl(c₂₃)*σ₁⁻¹ * inl(c₁_₂₃)
  -- Strategy: right-multiply both sides by σ(g₁g₂g₃), show both = σ₁*σ₂*σ₃.
  -- LHS proof: inl(c₁₂)*inl(c₁₂₃)*σ₁₂₃ = σ₁*σ₂*σ₃
  have lhs : S.inl (sectionCocycle S σ g₁ g₂) * S.inl (sectionCocycle S σ (g₁ * g₂) g₃) *
             σ.toFun (g₁ * g₂ * g₃) = σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ := by
    rw [mul_assoc, ← section_mul_eq S σ (g₁ * g₂) g₃,
        ← mul_assoc, ← section_mul_eq S σ g₁ g₂]
  -- RHS proof: (σ₁*inl(c₂₃)*σ₁⁻¹*inl(c₁_₂₃))*σ(g₁(g₂g₃)) = σ₁*σ₂*σ₃
  have rhs : (σ.toFun g₁ * S.inl (sectionCocycle S σ g₂ g₃) * (σ.toFun g₁)⁻¹ *
              S.inl (sectionCocycle S σ g₁ (g₂ * g₃))) *
             σ.toFun (g₁ * (g₂ * g₃)) = σ.toFun g₁ * σ.toFun g₂ * σ.toFun g₃ := by
    rw [mul_assoc _ (S.inl (sectionCocycle S σ g₁ (g₂ * g₃)))]
    rw [← section_mul_eq S σ g₁ (g₂ * g₃)]
    rw [mul_assoc _ (σ.toFun g₁)⁻¹, inv_mul_cancel_left]
    rw [mul_assoc, ← section_mul_eq S σ g₂ g₃, ← mul_assoc]
  apply mul_right_cancel (b := σ.toFun (g₁ * g₂ * g₃))
  rw [lhs, show g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) from mul_assoc g₁ g₂ g₃, rhs]

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
