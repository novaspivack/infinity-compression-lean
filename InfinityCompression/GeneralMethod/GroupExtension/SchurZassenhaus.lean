/-
  EPIC_019_GA1 — Splitting obstructions and the 2-cocycle in the fiber architecture.

  The key insight: every group extension has a set-theoretic section, but the existence of
  a homomorphic section (splitting) is additional algebraic structure. The **obstruction**
  to upgrading from set-theoretic to algebraic is measured by a 2-cocycle valued in N.

  We formalize:
  1. The 2-cocycle associated to any set-theoretic section of an extension.
  2. The splitting criterion: the extension splits iff the cocycle is trivial.
  3. Restriction of extensions to subgroups (local sections).
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import InfinityCompression.GeneralMethod.GroupExtension.FiberArchitecture

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

variable {N E G : Type u} [Group N] [Group E] [Group G]
variable (S : GroupExtension N E G)

/-! ### The 2-cocycle of a set-theoretic section

Given a section `σ : G → E` with `π ∘ σ = id`, define
  `c(g₁, g₂) := σ(g₁) · σ(g₂) · σ(g₁g₂)⁻¹`
which lies in `ker π = range(inl)`. We extract the N-valued preimage.
-/

private theorem section_defect_mem_range (σ : S.Section) (g₁ g₂ : G) :
    σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹ ∈ S.inl.range := by
  rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      σ.rightInverse_rightHom, σ.rightInverse_rightHom, σ.rightInverse_rightHom,
      mul_inv_cancel]

noncomputable def sectionCocycle (σ : S.Section) (g₁ g₂ : G) : N :=
  (section_defect_mem_range S σ g₁ g₂).choose

theorem sectionCocycle_spec (σ : S.Section) (g₁ g₂ : G) :
    S.inl (sectionCocycle S σ g₁ g₂) =
      σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹ :=
  (section_defect_mem_range S σ g₁ g₂).choose_spec

theorem section_mul_eq (σ : S.Section) (g₁ g₂ : G) :
    σ.toFun g₁ * σ.toFun g₂ = S.inl (sectionCocycle S σ g₁ g₂) * σ.toFun (g₁ * g₂) := by
  have h := sectionCocycle_spec S σ g₁ g₂
  rw [eq_mul_inv_iff_mul_eq] at h
  exact h.symm

/-! ### Splitting iff the cocycle is trivial -/

theorem splits_iff_trivial_cocycle :
    Nonempty S.Splitting ↔
    ∃ σ : S.Section, ∀ g₁ g₂ : G, sectionCocycle S σ g₁ g₂ = 1 := by
  constructor
  · rintro ⟨s⟩
    refine ⟨s.toSection, fun g₁ g₂ => ?_⟩
    apply S.inl_injective
    rw [sectionCocycle_spec, map_one]
    show s.toFun g₁ * s.toFun g₂ * (s.toFun (g₁ * g₂))⁻¹ = 1
    rw [s.map_mul', mul_inv_cancel]
  · rintro ⟨σ, hσ⟩
    refine ⟨{
      toFun := σ.toFun
      map_one' := by
        have spec := section_mul_eq S σ 1 1
        rw [hσ 1 1, map_one, one_mul, mul_one] at spec
        have h : σ.toFun 1 * σ.toFun 1 = σ.toFun 1 := spec
        calc σ.toFun 1 = σ.toFun 1 * σ.toFun 1 * (σ.toFun 1)⁻¹ := by group
          _ = σ.toFun 1 * (σ.toFun 1)⁻¹ := by rw [h]
          _ = 1 := mul_inv_cancel _
      map_mul' := fun g₁ g₂ => by
        have spec := section_mul_eq S σ g₁ g₂
        rw [hσ g₁ g₂, map_one, one_mul] at spec
        exact spec.symm
      rightInverse_rightHom := σ.rightInverse_rightHom
    }⟩

/-! ### Architecture reading

  The 2-cocycle `sectionCocycle S σ` measures the **gap** between the set-theoretic
  section (which always exists — the bare layer) and a homomorphic section (the enriched
  layer). The extension splits iff this gap vanishes for some choice of section.

  This makes the positive-closure architecture's central distinction — between bare
  (set-theoretic) and enriched (algebraic) sections — **load-bearing**: the cocycle
  is the precise invariant that separates the two layers.
-/

end InfinityCompression.GeneralMethod
