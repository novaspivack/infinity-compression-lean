/-
  EPIC_021_NR1 — Central extensions and the Schur multiplier concept.

  A central extension `1 → A → E → G → 1` has `A` in the center of `E`.
  The Schur multiplier `H²(G, A)` classifies such extensions.

  We formalize:
  1. Central extensions as a predicate on group extensions.
  2. The centrality condition implies the cocycle is "abelian" (commutes with everything).
  3. S₃ = Perm(Fin 3) as a concrete group for multiplier computations.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.Perm.Fin
import InfinityCompression.GeneralMethod.GroupExtension.SchurZassenhaus

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

variable {N E G : Type u} [Group N] [Group E] [Group G]

/-! ### Central extensions -/

def IsCentralExtension (S : GroupExtension N E G) : Prop :=
  ∀ (n : N) (e : E), S.inl n * e = e * S.inl n

theorem centralExtension_inl_comm (S : GroupExtension N E G)
    (hc : IsCentralExtension S) (n : N) (e : E) :
    S.inl n * e = e * S.inl n :=
  hc n e

theorem centralExtension_cocycle_central (S : GroupExtension N E G)
    (hc : IsCentralExtension S) (σ : S.Section) (g₁ g₂ : G) :
    S.inl (sectionCocycle S σ g₁ g₂) * σ.toFun g₁ =
    σ.toFun g₁ * S.inl (sectionCocycle S σ g₁ g₂) := by
  exact hc (sectionCocycle S σ g₁ g₂) (σ.toFun g₁)

/-! ### Central extensions have abelian image

If the extension is central, the image of N commutes with everything in E,
so in particular the image is abelian (as a subgroup of the center).
-/

theorem centralExtension_image_comm (S : GroupExtension N E G)
    (hc : IsCentralExtension S) (n₁ n₂ : N) :
    S.inl n₁ * S.inl n₂ = S.inl n₂ * S.inl n₁ :=
  hc n₁ (S.inl n₂)

/-! ### S₃ = Perm(Fin 3) -/

abbrev S₃ := Equiv.Perm (Fin 3)

theorem S₃_not_abelian :
    ¬∀ (a b : S₃), a * b = b * a := by
  push_neg
  exact ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩

/-! ### Architecture reading

  Central extensions are the cleanest case of the fiber architecture:

  | Property | Central extension | General extension |
  |----------|-------------------|-------------------|
  | Kernel position | Center of E | Normal in E |
  | Conjugation action | Trivial | Nontrivial |
  | Cocycle commutativity | Commutes with sections | May not commute |
  | Classification | H²(G, A) (abelian cohomology) | Non-abelian H² |
  | Schur multiplier | Universal classifier | Not applicable |

  The fiber architecture makes this hierarchy visible:
  - Central = cocycle is "abelian" = clean classification.
  - Non-central = cocycle involves conjugation = richer obstruction theory.
  - The Q₈ boundary (NonAbelianObstruction.lean) shows where centrality fails.
-/

end InfinityCompression.GeneralMethod
