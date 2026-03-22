/-
  EPIC_022_OP1 — Nerve of a category with a terminal object: vertex and constant map.

  If C has a terminal object t, the nerve of C has a distinguished 0-simplex (the
  vertex t) and a constant map at that vertex. The unique morphisms c → t for all
  c ∈ C witness that the nerve deformation-retracts to this vertex.

  **What is proved (zero sorry):**
  - The terminal object gives a 0-simplex in the nerve.
  - The constant map on the nerve at the terminal vertex.
  - Unique morphisms to the terminal object.

  **What remains for full contractibility:**
  The simplicial homotopy id ≃ const(t) requires constructing a map
  Δ[1] × nerve C → nerve C using the ComposableArrows API, which is
  nontrivial with current Mathlib infrastructure.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Category.Preorder

universe u

namespace InfinityCompression.GeneralMethod.Quillen

open CategoryTheory CategoryTheory.Limits SimplexCategory

variable {C : Type u} [SmallCategory C]

noncomputable def nerveTerminalVertex (t : C) (_ : IsTerminal t) :
    (nerve C).obj (Opposite.op (mk 0)) :=
  ComposableArrows.mk₀ t

noncomputable def nerveConstAtTerminal (t : C) (ht : IsTerminal t) :
    nerve C ⟶ nerve C :=
  SSet.const (nerveTerminalVertex t ht)

noncomputable def terminalMorphism (t : C) (ht : IsTerminal t) (c : C) : c ⟶ t :=
  ht.from c

theorem terminalMorphism_unique (t : C) (ht : IsTerminal t) (c : C)
    (f g : c ⟶ t) : f = g :=
  ht.hom_ext f g

/-! ### For preorders with OrderTop, ⊤ is terminal -/

noncomputable def preorder_top_isTerminal (α : Type u) [Preorder α] [OrderTop α] :
    IsTerminal (⊤ : α) :=
  isTerminalTop

end InfinityCompression.GeneralMethod.Quillen
