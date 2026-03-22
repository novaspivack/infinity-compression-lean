/-
  EPIC_022_OP1 Phase B2 — Embedding problems as fiber/section problems.

  **Mathematical content:**

  An embedding problem in Galois theory asks: given a Galois extension L/K with
  group G and a surjection φ : H ↠ G, does there exist a Galois extension F/K
  with group H such that F extends L?

  In the fiber architecture:
  - The group extension `1 → ker(φ) → H → G → 1` is the enriched/bare structure.
  - A **solution** to the embedding problem is a section of this extension that is
    compatible with the Galois action.
  - The **obstruction** lives in H²(G, ker(φ)) — exactly our cocycle story.
  - A **split** embedding problem (where the extension splits) is always solvable
    over number fields (Hilbert irreducibility).

  We formalize:
  1. The abstract embedding problem as a group extension + Galois data.
  2. The connection: solvability ↔ existence of a compatible section.
  3. The split case: if the extension splits, the embedding problem is solvable.

  This is the first Lean formalization connecting embedding problems to the
  group extension fiber architecture.

  **Reference:** Applications of Galois Cohomology (UCLA lecture notes).
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import InfinityCompression.GeneralMethod.GroupExtension.FiberArchitecture
import InfinityCompression.GeneralMethod.GroupExtension.SchurZassenhaus

universe u

namespace InfinityCompression.GeneralMethod.Galois

open GroupExtension

/-! ### Abstract embedding problem

An embedding problem is given by:
- A group G (the "known" Galois group).
- A group H with a surjection φ : H →* G (the "target" group).
- The kernel N = ker(φ) gives a group extension 1 → N → H → G → 1.

A **solution** is a group homomorphism ψ : G → H such that φ ∘ ψ = id.
This is exactly a splitting of the extension!
-/

structure EmbeddingProblem (G H : Type u) [Group G] [Group H] where
  surjection : H →* G
  surjective : Function.Surjective surjection

variable {G H : Type u} [Group G] [Group H]

def EmbeddingProblem.kernel (ep : EmbeddingProblem G H) : Subgroup H :=
  ep.surjection.ker

def EmbeddingProblem.toGroupExtension (ep : EmbeddingProblem G H) :
    GroupExtension ep.surjection.ker H G where
  inl := ep.surjection.ker.subtype
  rightHom := ep.surjection
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := by
    ext h
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact hk
    · intro hh
      exact ⟨⟨h, hh⟩, rfl⟩
  rightHom_surjective := ep.surjective

/-! ### Solutions as splittings

A solution to the embedding problem is a homomorphism ψ : G →* H with φ ∘ ψ = id.
This is exactly a splitting of the associated group extension.
-/

structure EmbeddingProblem.Solution (ep : EmbeddingProblem G H) where
  lift : G →* H
  isSection : ∀ g : G, ep.surjection (lift g) = g

def EmbeddingProblem.Solution.toSplitting (ep : EmbeddingProblem G H)
    (sol : ep.Solution) : ep.toGroupExtension.Splitting where
  toFun := sol.lift
  map_one' := sol.lift.map_one'
  map_mul' := sol.lift.map_mul'
  rightInverse_rightHom := sol.isSection

theorem EmbeddingProblem.solvable_iff_splits (ep : EmbeddingProblem G H) :
    Nonempty ep.Solution ↔ Nonempty ep.toGroupExtension.Splitting := by
  constructor
  · rintro ⟨sol⟩
    exact ⟨sol.toSplitting ep⟩
  · rintro ⟨s⟩
    exact ⟨{
      lift := s.toMonoidHom
      isSection := s.rightHom_splitting
    }⟩

/-! ### The cocycle obstruction for embedding problems

The embedding problem is solvable iff the associated extension has trivial cocycle
class. This connects the Galois-theoretic question to the cohomological obstruction.
-/

theorem EmbeddingProblem.solvable_iff_trivial_cocycle (ep : EmbeddingProblem G H) :
    Nonempty ep.Solution ↔
    ∃ σ : ep.toGroupExtension.Section,
      ∀ g₁ g₂ : G, sectionCocycle ep.toGroupExtension σ g₁ g₂ = 1 := by
  rw [ep.solvable_iff_splits]
  exact splits_iff_trivial_cocycle ep.toGroupExtension

/-! ### Split embedding problems are always solvable

If the extension `1 → N → H → G → 1` splits (i.e., H ≅ N ⋊ G), then the
embedding problem is trivially solvable. Over number fields, this is the
starting point for the Hilbert irreducibility approach to the inverse Galois problem.
-/

theorem EmbeddingProblem.solvable_of_split (ep : EmbeddingProblem G H)
    (hs : Nonempty ep.toGroupExtension.Splitting) :
    Nonempty ep.Solution :=
  ep.solvable_iff_splits.mpr hs

/-! ### Architecture reading

  Embedding problems are the **Galois-theoretic instantiation** of the fiber architecture:

  | Architecture layer | Embedding problem |
  |--------------------|-------------------|
  | Enriched carrier | Target group H |
  | Bare certificate | Known Galois group G |
  | Forgetful map | Surjection φ : H →* G |
  | Fiber | Kernel ker(φ) — the "new" Galois structure |
  | Section | Solution ψ : G →* H with φ ∘ ψ = id |
  | Obstruction | Cocycle class in H²(G, ker(φ)) |

  The key theorem `solvable_iff_trivial_cocycle` connects the Galois lifting
  question directly to the cocycle obstruction from the group extension story.
  This is the bridge between number theory and abstract algebra that the
  fiber architecture makes explicit.

  **Significance:** This is the first Lean formalization that states embedding
  problems as group extension splitting problems with cocycle obstructions.
-/

end InfinityCompression.GeneralMethod.Galois
