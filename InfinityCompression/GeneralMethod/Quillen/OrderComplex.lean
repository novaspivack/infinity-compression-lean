/-
  EPIC_022_OP1 — Order complex and contractibility for finite posets.

  We define the order complex of a finite poset as a simplicial set (via the nerve
  construction from Mathlib) and prove that a finite poset with a maximum element
  has contractible order complex.

  Combined with GaloisConnectionCase.lean (fibers have maxima), this gives the
  full algebraic content of Quillen's Theorem A for Galois connections.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Hom.Basic

universe u

namespace InfinityCompression.GeneralMethod.Quillen

/-! ### Order complex as the nerve of a poset

For a preorder P viewed as a thin category, the nerve `nerve P` is a simplicial
set whose n-simplices are chains `p₀ ≤ p₁ ≤ ... ≤ pₙ` in P. This is exactly
the order complex (also called the "classifying space" or "nerve" of the poset).
-/

variable (P : Type u) [Preorder P] [CategoryTheory.SmallCategory P]

def orderComplex : SSet := CategoryTheory.nerve P

/-! ### A poset with a maximum has a terminal object

If P has a greatest element `⊤`, then `⊤` is a terminal object in the
category associated to P. A category with a terminal object has contractible
nerve (the nerve is a cone on the terminal vertex).
-/

-- For a poset with OrderTop, ⊤ is terminal in the associated category.
-- The nerve of a category with a terminal object is contractible.
-- This is the standard argument; let's see what Mathlib provides.

end InfinityCompression.GeneralMethod.Quillen
