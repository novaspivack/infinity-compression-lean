/-
  Quillen's Theorem A for Galois connections — homotopy data.

  For a Galois connection (l, u) between partial orders, this file constructs
  the nerve maps and the explicit 1-simplex witnesses (closure and kernel edges)
  that constitute the homotopy data for Quillen's Theorem A.

  **Scope and gap:** The construction is complete with zero sorry. The remaining
  step — proving that the composition of nerve maps is homotopic to the identity
  using this data — requires simplicial homotopy as a type, which is not yet in
  Mathlib. The `quillenAData` structure packages everything needed for that step.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.CategoryTheory.Category.Preorder

universe u

namespace InfinityCompression.GeneralMethod.Quillen

open CategoryTheory

section QuillenA

variable {P : Type u} {Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {l : P → Q} {u : Q → P}

noncomputable def lFunctor (gc : GaloisConnection l u) : P ⥤ Q where
  obj := l
  map := fun {a b} h => homOfLE (gc.monotone_l (leOfHom h))

noncomputable def uFunctor (gc : GaloisConnection l u) : Q ⥤ P where
  obj := u
  map := fun {a b} h => homOfLE (gc.monotone_u (leOfHom h))

noncomputable def nerveL (gc : GaloisConnection l u) : nerve P ⟶ nerve Q :=
  nerveMap (lFunctor gc)

noncomputable def nerveU (gc : GaloisConnection l u) : nerve Q ⟶ nerve P :=
  nerveMap (uFunctor gc)

noncomputable def closureEdge (gc : GaloisConnection l u) (p : P) :
    ComposableArrows P 1 :=
  ComposableArrows.mk₁ (homOfLE (gc.le_u_l p))

noncomputable def kernelEdge (gc : GaloisConnection l u) (q : Q) :
    ComposableArrows Q 1 :=
  ComposableArrows.mk₁ (homOfLE (gc.l_u_le q))

theorem closureEdge_source (gc : GaloisConnection l u) (p : P) :
    (closureEdge gc p).obj 0 = p := rfl

theorem closureEdge_target (gc : GaloisConnection l u) (p : P) :
    (closureEdge gc p).obj 1 = u (l p) := rfl

theorem kernelEdge_source (gc : GaloisConnection l u) (q : Q) :
    (kernelEdge gc q).obj 0 = l (u q) := rfl

theorem kernelEdge_target (gc : GaloisConnection l u) (q : Q) :
    (kernelEdge gc q).obj 1 = q := rfl

/-! ### Homotopy data for Quillen's Theorem A (Galois connection case) -/

structure QuillenAData (l : P → Q) (u : Q → P) where
  forward : nerve P ⟶ nerve Q
  backward : nerve Q ⟶ nerve P
  left_edge : ∀ p : P, ComposableArrows P 1
  right_edge : ∀ q : Q, ComposableArrows Q 1
  left_source : ∀ p, (left_edge p).obj 0 = p
  left_target : ∀ p, (left_edge p).obj 1 = u (l p)
  right_source : ∀ q, (right_edge q).obj 0 = l (u q)
  right_target : ∀ q, (right_edge q).obj 1 = q

/-- **Homotopy data for Quillen's Theorem A (Galois connection case).**

For a Galois connection `(l, u)` between partial orders, this packages the
nerve maps and explicit 1-simplex witnesses needed for Quillen's Theorem A:
- `forward`/`backward`: the nerve maps induced by `l` and `u`.
- Closure edges `[p → u(l(p))]` witnessing `u ∘ l ≥ id` on nerve P.
- Kernel edges `[l(u(q)) → q]` witnessing `l ∘ u ≤ id` on nerve Q.

The remaining step (composition homotopic to identity) requires simplicial
homotopy as a Lean type, which is not yet available in Mathlib. -/
-- `quillenA` renamed to `quillenAData` to accurately reflect scope
noncomputable def quillenAData (gc : GaloisConnection l u) :
    QuillenAData l u where
  forward := nerveL gc
  backward := nerveU gc
  left_edge := closureEdge gc
  right_edge := kernelEdge gc
  left_source := fun _ => rfl
  left_target := fun _ => rfl
  right_source := fun _ => rfl
  right_target := fun _ => rfl

end QuillenA

end InfinityCompression.GeneralMethod.Quillen
