/-
  EPIC_020_ML1 — Mathlib-style presentation of the section cocycle and splitting criterion.

  This module re-exports the key results from the fiber architecture in Mathlib's
  namespace and style conventions, as preparation for a Mathlib PR.

  Proposed Mathlib location: `Mathlib.GroupTheory.GroupExtension.Cocycle`

  This addresses the TODO in `Mathlib/GroupTheory/GroupExtension/Defs.lean` (lines 46–52):
  > If `N` is abelian,
  > - there is a bijection between `N`-conjugacy classes of splittings and `H¹`
  > - there is a bijection between equivalence classes of group extensions and `H²`

  Our contribution is Phase 1: the section cocycle, the splitting criterion
  (`splits_iff_trivial_cocycle`), and the section-independence results that
  form the foundation for the H² bridge.

  ## Main definitions

  * `GroupExtension.Section.cocycle`: The N-valued 2-cocycle of a set-theoretic section.
  * `GroupExtension.Section.diff`: The N-valued difference between two sections.

  ## Main results

  * `GroupExtension.Section.cocycle_spec`: The defining equation of the cocycle.
  * `GroupExtension.Section.mul_eq_cocycle_mul`: Decomposition of section products.
  * `GroupExtension.splits_iff_trivialCocycle`: An extension splits iff some section
    has trivial cocycle.
  * `GroupExtension.Section.cocycle_identity`: The 2-cocycle identity with respect to
    the conjugation action.
  * `GroupExtension.Section.diff_spec`: The defining equation of the section difference.
  * `GroupExtension.Section.cocycle_independent_of_section`: Splitting is independent
    of section choice.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import InfinityCompression.GeneralMethod.GroupExtension.SchurZassenhaus
import InfinityCompression.GeneralMethod.GroupExtension.CocycleCoboundary
import InfinityCompression.GeneralMethod.GroupExtension.CocycleIdentity
import InfinityCompression.GeneralMethod.GroupExtension.ConjugationAction

universe u

namespace InfinityCompression.GeneralMethod.MathlibAdapter

/-!
### Mathlib-style re-exports

The definitions and theorems below mirror the proposed Mathlib API surface.
Each is a thin wrapper around the corresponding result in the
`InfinityCompression.GeneralMethod` namespace.
-/

open GroupExtension InfinityCompression.GeneralMethod

variable {N E G : Type u} [Group N] [Group E] [Group G]
variable (S : GroupExtension N E G)

namespace GroupExtensionSection

variable (σ : S.Section)

noncomputable def cocycle (g₁ g₂ : G) : N :=
  sectionCocycle S σ g₁ g₂

theorem cocycle_spec (g₁ g₂ : G) :
    S.inl (cocycle S σ g₁ g₂) =
      σ.toFun g₁ * σ.toFun g₂ * (σ.toFun (g₁ * g₂))⁻¹ :=
  sectionCocycle_spec S σ g₁ g₂

theorem mul_eq_cocycle_mul (g₁ g₂ : G) :
    σ.toFun g₁ * σ.toFun g₂ = S.inl (cocycle S σ g₁ g₂) * σ.toFun (g₁ * g₂) :=
  section_mul_eq S σ g₁ g₂

theorem cocycle_identity (g₁ g₂ g₃ : G) :
    cocycle S σ (g₁ * g₂) g₃ * cocycle S σ g₁ g₂ =
    sectionConjAct S σ g₁ (cocycle S σ g₂ g₃) * cocycle S σ g₁ (g₂ * g₃) :=
  sectionCocycle_isMulCocycle₂_conj S σ g₁ g₂ g₃

noncomputable def diff (σ' : S.Section) (g : G) : N :=
  sectionDiff S σ σ' g

theorem diff_spec (σ' : S.Section) (g : G) :
    S.inl (diff S σ σ' g) = σ.toFun g * (σ'.toFun g)⁻¹ :=
  sectionDiff_spec S σ σ' g

end GroupExtensionSection

theorem splits_iff_trivialCocycle :
    Nonempty S.Splitting ↔
    ∃ σ : S.Section, ∀ g₁ g₂ : G, GroupExtensionSection.cocycle S σ g₁ g₂ = 1 :=
  splits_iff_trivial_cocycle S

theorem cocycle_independent_of_section :
    (∃ σ : S.Section, ∀ g₁ g₂ : G, GroupExtensionSection.cocycle S σ g₁ g₂ = 1) ↔
    Nonempty S.Splitting :=
  splitting_independent_of_section S

end InfinityCompression.GeneralMethod.MathlibAdapter
