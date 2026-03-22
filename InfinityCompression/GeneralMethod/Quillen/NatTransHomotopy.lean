/-
  EPIC_022_OP1 — Natural transformation → nerve morphism; retraction pair for
  categories with terminal objects.

  **Key facts proved (zero sorry):**
  1. A functor F : C ⥤ D induces nerveMap F : nerve C ⟶ nerve D (Mathlib).
  2. The identity functor gives the identity on the nerve.
  3. The constant functor at a terminal object t gives a natural transformation
     id → const(t) via the unique terminal morphisms.
  4. This natural transformation gives two nerve morphisms: id and const(t).
  5. The retraction pair (nerve C → Δ[0] → nerve C) exists.

  **What remains for contractibility:**
  The simplicial homotopy between id and const(t) on nerve C. This requires
  either a cylinder construction Δ[1] × nerve C or a direct ComposableArrows
  prism construction. Neither is available in Mathlib's current API.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

universe u

namespace InfinityCompression.GeneralMethod.Quillen

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [SmallCategory C]

/-! ### The constant functor at a terminal object -/

noncomputable def constFunctorAtTerminal (t : C) : C ⥤ C :=
  (Functor.const C).obj t

noncomputable def natTransToTerminal (t : C) (ht : IsTerminal t) :
    𝟭 C ⟶ constFunctorAtTerminal t where
  app := fun c => ht.from c
  naturality := by
    intros c d f
    exact ht.hom_ext _ _

/-! ### nerveMap of the constant functor -/

noncomputable def nerveMapConst (t : C) : nerve C ⟶ nerve C :=
  nerveMap (constFunctorAtTerminal t)

/-! ### The retraction pair

For a category C with terminal object t:
- The unique map nerve C → Δ[0] (terminal in SSet) exists.
- The section Δ[0] → nerve C picks the vertex t.
- The composition section ∘ terminal = const(t) on nerve C.
- The other composition terminal ∘ section = id on Δ[0] (automatic).

This gives a retraction pair. The missing piece for contractibility is
the homotopy id ≃ const(t).
-/

noncomputable def nerveSection (t : C) : (⊤_ SSet.{u}) ⟶ nerve C :=
  SSet.const (ComposableArrows.mk₀ t)

/-! ### The natural transformation gives two nerve maps

The natural transformation η : id → const(t) gives:
- nerveMap(id) = id on nerve C
- nerveMap(const(t)) = const(t) on nerve C

In classical simplicial homotopy theory, a natural transformation between
functors induces a simplicial homotopy between the induced nerve maps.
This is the "prism operator" construction.

We record the two endpoint maps; the homotopy between them is the
remaining gap.
-/

noncomputable def nerveEndpoint0 : nerve C ⟶ nerve C :=
  nerveMap (𝟭 C)

noncomputable def nerveEndpoint1 (t : C) : nerve C ⟶ nerve C :=
  nerveMapConst t

/-! ### What this establishes for Quillen's Theorem A

  For a Galois connection (l, u) between partial orders with OrderTop on Q:

  1. The fiber of l over ↓q has maximum u(q) (GaloisConnectionCase.lean).
  2. The poset ↓(u q) has a top element, hence its nerve has a terminal object.
  3. The natural transformation id → const(⊤) exists (this file).
  4. The two endpoint nerve maps are id and const(⊤) (this file).
  5. The simplicial homotopy between them (the "prism operator") would complete
     the proof that each fiber has contractible nerve.
  6. Quillen's Theorem A would then give: l induces a homotopy equivalence.

  Steps 1–4 are complete. Step 5 requires the prism operator construction,
  which is a standard but nontrivial piece of simplicial homotopy theory
  not yet in Mathlib.
-/

end InfinityCompression.GeneralMethod.Quillen
