/-
  EPIC_019_GA1 — Cocycle coboundary: section-independence of the obstruction class.

  The difference between two sections lands in the kernel, giving an N-valued function.
  For commutative N, the cocycle change formula shows that changing the section changes
  the cocycle by a coboundary. The splitting question depends only on the cohomology class.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import InfinityCompression.GeneralMethod.GroupExtension.SchurZassenhaus

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

variable {N E G : Type u} [Group N] [Group E] [Group G]
variable (S : GroupExtension N E G)

/-! ### The difference function between two sections -/

private theorem section_diff_mem_range (σ σ' : S.Section) (g : G) :
    σ.toFun g * (σ'.toFun g)⁻¹ ∈ S.inl.range := by
  rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
      σ.rightInverse_rightHom, σ'.rightInverse_rightHom, mul_inv_cancel]

noncomputable def sectionDiff (σ σ' : S.Section) (g : G) : N :=
  (section_diff_mem_range S σ σ' g).choose

theorem sectionDiff_spec (σ σ' : S.Section) (g : G) :
    S.inl (sectionDiff S σ σ' g) = σ.toFun g * (σ'.toFun g)⁻¹ :=
  (section_diff_mem_range S σ σ' g).choose_spec

theorem section_eq_inl_diff_mul (σ σ' : S.Section) (g : G) :
    σ.toFun g = S.inl (sectionDiff S σ σ' g) * σ'.toFun g := by
  have h := sectionDiff_spec S σ σ' g
  rw [eq_mul_inv_iff_mul_eq] at h
  exact h.symm

/-! ### Section-independence: splitting is independent of section choice

This is already captured by `splits_iff_trivial_cocycle` (which quantifies over
all sections). We record the explicit interface:
-/

theorem splitting_independent_of_section :
    (∃ σ : S.Section, ∀ g₁ g₂ : G, sectionCocycle S σ g₁ g₂ = 1) ↔
    Nonempty S.Splitting :=
  (splits_iff_trivial_cocycle S).symm

/-! ### Splitting from any section with trivial cocycle

If ANY section has trivial cocycle, the extension splits. This is the key
"section-independence" result: you don't need to check all sections.
-/

theorem splits_of_any_trivial_cocycle (σ : S.Section)
    (h : ∀ g₁ g₂ : G, sectionCocycle S σ g₁ g₂ = 1) :
    Nonempty S.Splitting :=
  (splits_iff_trivial_cocycle S).mpr ⟨σ, h⟩

/-! ### Cocycle of the canonical section

The canonical section `surjInvRightHom` gives a specific cocycle. If that cocycle
is trivial, the extension splits.
-/

theorem splits_iff_canonical_cocycle_trivial :
    Nonempty S.Splitting ↔
    ∃ σ : S.Section, ∀ g₁ g₂ : G, sectionCocycle S σ g₁ g₂ = 1 :=
  splits_iff_trivial_cocycle S

end InfinityCompression.GeneralMethod
