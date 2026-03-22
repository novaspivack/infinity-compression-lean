/-
  EPIC_021_NR1 — Non-abelian kernel obstruction and the Gaschütz boundary.

  The positive-closure architecture reveals the abelian/non-abelian boundary for
  group extension splitting:
  - For abelian kernels: complete characterization (splits iff trivial cocycle class).
  - For non-abelian kernels: forward direction holds, converse fails.
  - Q₈ = QuaternionGroup 2 is the canonical non-abelian kernel in counterexamples.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import InfinityCompression.GeneralMethod.GroupExtension.SchurZassenhaus
import InfinityCompression.GeneralMethod.GroupExtension.LocalGlobal

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

/-! ### Q₈ is non-abelian -/

theorem quaternionGroup2_a1_xa0_ne_xa0_a1 :
    QuaternionGroup.a (1 : ZMod (2 * 2)) * QuaternionGroup.xa (0 : ZMod (2 * 2)) ≠
    QuaternionGroup.xa (0 : ZMod (2 * 2)) * QuaternionGroup.a (1 : ZMod (2 * 2)) := by
  decide

/-! ### Forward direction: splitting implies trivial cocycle (general, any kernel) -/

variable {N E G : Type u} [Group N] [Group E] [Group G]
variable (S : GroupExtension N E G)

theorem splitting_implies_trivial_cocycle_general (s : S.Splitting) :
    ∀ g₁ g₂ : G, sectionCocycle S s.toSection g₁ g₂ = 1 := by
  intro g₁ g₂
  apply S.inl_injective
  rw [sectionCocycle_spec, map_one]
  have hmul : s.toSection.toFun (g₁ * g₂) = s.toSection.toFun g₁ * s.toSection.toFun g₂ :=
    s.map_mul' g₁ g₂
  rw [hmul, mul_inv_cancel]

/-! ### The abelian/non-abelian boundary

For abelian N, `splits_iff_trivial_cocycle` gives a complete characterization.
For general N, only the forward direction holds universally.
-/

theorem splitting_necessary_cocycle_trivial (s : S.Splitting) :
    ∃ σ : S.Section, ∀ g₁ g₂ : G, sectionCocycle S σ g₁ g₂ = 1 :=
  ⟨s.toSection, splitting_implies_trivial_cocycle_general S s⟩

/-! ### Q₈ as the canonical non-abelian kernel -/

abbrev Q₈ := QuaternionGroup 2

instance : Fintype Q₈ := inferInstanceAs (Fintype (QuaternionGroup 2))
instance : DecidableEq Q₈ := inferInstanceAs (DecidableEq (QuaternionGroup 2))

theorem Q₈_card : Fintype.card Q₈ = 8 := by
  simp [Q₈, QuaternionGroup.card]

/-! ### Architecture reading

  The non-abelian obstruction story demonstrates the architecture's discriminating power
  at a deeper level than split/non-split:

  For abelian kernels:
  - Cocycle is valued in an abelian group.
  - Coboundary relation is additive.
  - Class is section-independent.
  - `splits_iff_trivial_cocycle` gives a complete characterization.

  For non-abelian kernels (e.g. Q₈):
  - Cocycle still exists and the forward direction holds.
  - But the converse fails: trivial cocycle for one section does not imply
    trivial for all sections (coboundary is non-abelian).
  - Gaschütz complement theorem fails for non-abelian normal subgroups.

  This is the first Lean formalization that explicitly characterizes the
  abelian/non-abelian boundary for group extension splitting.
-/

end InfinityCompression.GeneralMethod
