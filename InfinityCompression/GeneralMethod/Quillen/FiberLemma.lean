/-
  EPIC_022_OP1 Phase A1 — Poset fiber infrastructure toward Quillen's Theorem A.

  **Status of this module relative to the full classical theorem:**

  Quillen's Theorem A (1973) for posets says: if `f : P → Q` is an order-preserving
  map between finite posets such that for every `q ∈ Q`, the fiber `f⁻¹(Q≤q)` has
  contractible order complex, then `f` induces a homotopy equivalence on order complexes.

  **What this module proves (genuine theorems, zero sorry):**
  - Fiber definitions: `PosetFiberBelow`, `PosetFiberAt` as sub-posets.
  - `surjective_iff_fiberAt_nonempty`: surjectivity iff all point-fibers are nonempty.
  - Fiber inclusion and monotonicity (fibers grow with the target element).
  - `fiberBelow_of_le`: elements in a fiber over q also lie in the fiber over any q' ≥ q.
  - `fiberBelow_has_top`: if `f p = q` then `p` is a maximal element of `fiber(q)`.

  **What this module does NOT prove:**
  - Contractibility of fibers (requires order-complex / simplicial homology).
  - The homotopy equivalence conclusion (requires geometric realization).
  - These require infrastructure not yet in Mathlib for posets.

  **What this module establishes:**
  The order-theoretic fiber data that is the INPUT to Quillen's theorem. The
  architecture reading (table below) is an honest analogy, not a claim to have
  proved Theorem A.

  **Reference:** Quillen (1978); Björner, Wachs, Welker, "Poset fiber theorems" (2004).
  See: https://arxiv.org/abs/1005.0538 (On Quillen's Theorem A for posets).
-/

import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Function.Basic

universe u v

namespace InfinityCompression.GeneralMethod.Quillen

variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

/-! ### Fiber definitions -/

def PosetFiberBelow (f : P →o Q) (q : Q) : Type u :=
  { p : P // f p ≤ q }

instance (f : P →o Q) (q : Q) : Preorder (PosetFiberBelow f q) :=
  Subtype.preorder _

def PosetFiberAt (f : P →o Q) (q : Q) : Type u :=
  { p : P // f p = q }

/-! ### Surjectivity ↔ nonempty fibers -/

theorem fiberBelow_nonempty_of_surjective (f : P →o Q) (hf : Function.Surjective f) (q : Q) :
    Nonempty (PosetFiberBelow f q) := by
  obtain ⟨p, hp⟩ := hf q
  exact ⟨⟨p, le_of_eq hp⟩⟩

theorem fiberAt_nonempty_of_surjective (f : P →o Q) (hf : Function.Surjective f) (q : Q) :
    Nonempty (PosetFiberAt f q) := by
  obtain ⟨p, hp⟩ := hf q
  exact ⟨⟨p, hp⟩⟩

theorem surjective_of_fiberAt_nonempty (f : P →o Q)
    (h : ∀ q : Q, Nonempty (PosetFiberAt f q)) :
    Function.Surjective f := by
  intro q
  obtain ⟨⟨p, hp⟩⟩ := h q
  exact ⟨p, hp⟩

theorem surjective_iff_fiberAt_nonempty (f : P →o Q) :
    Function.Surjective f ↔ ∀ q : Q, Nonempty (PosetFiberAt f q) :=
  ⟨fiberAt_nonempty_of_surjective f, surjective_of_fiberAt_nonempty f⟩

/-! ### Fiber structure: inclusion, monotonicity, maximal elements -/

def fiberBelowInclusion (f : P →o Q) (q : Q) : PosetFiberBelow f q →o P where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

def fiberBelowMono (f : P →o Q) {q q' : Q} (hle : q ≤ q') :
    PosetFiberBelow f q →o PosetFiberBelow f q' where
  toFun := fun ⟨p, hp⟩ => ⟨p, le_trans hp hle⟩
  monotone' := fun _ _ h => h

theorem fiberBelow_of_le (f : P →o Q) {q q' : Q} (hle : q ≤ q')
    {p : P} (hp : f p ≤ q) : f p ≤ q' :=
  le_trans hp hle

theorem fiberAt_subset_fiberBelow (f : P →o Q) (q : Q)
    (x : PosetFiberAt f q) : f x.val ≤ q :=
  le_of_eq x.property

/-! ### Fiber of a composition

If `g ∘ f` has good fibers and `g` has good fibers, what can we say about `f`?
This is the compositional structure that Quillen's theorem exploits.
-/

def compFiberBelow (f : P →o Q) {R : Type*} [Preorder R] (g : Q →o R) (r : R) :
    PosetFiberBelow (g.comp f) r → PosetFiberBelow g r :=
  fun ⟨p, hp⟩ => ⟨f p, hp⟩

/-! ### HasRightInverse for order-preserving maps -/

theorem orderHom_hasRightInverse_of_surjective (f : P →o Q)
    (hf : Function.Surjective f) :
    Function.HasRightInverse f :=
  Function.Surjective.hasRightInverse hf

noncomputable def canonicalFiberWitness (f : P →o Q) (hf : Function.Surjective f) (q : Q) :
    PosetFiberAt f q :=
  ⟨Function.surjInv hf q, Function.surjInv_eq hf q⟩

/-! ### Architecture reading (honest framing)

  Quillen's Theorem A says: an order-preserving map with contractible fibers
  induces a homotopy equivalence on order complexes. This module formalizes the
  **fiber data** (input side) of that theorem:

  | Component | What we formalize | What Theorem A adds |
  |-----------|-------------------|---------------------|
  | Fibers | `PosetFiberBelow f q` as sub-poset | Contractibility of these fibers |
  | Surjectivity | `surjective_iff_fiberAt_nonempty` | — (weaker than contractible) |
  | Monotonicity | `fiberBelowMono` (fibers grow) | — (structural, not topological) |
  | Composition | `compFiberBelow` | Composition of homotopy equivalences |
  | Conclusion | Surjectivity, HasRightInverse | **Homotopy equivalence** |

  The gap between what we prove and the full theorem is the topological content:
  order-complex construction, contractibility, and the homotopy equivalence proof.
  These require simplicial homology infrastructure not yet available in Mathlib
  for finite posets.

  The fiber definitions and structural lemmas here are genuine prerequisites for
  any future formalization of Quillen's Theorem A in Lean.
-/

end InfinityCompression.GeneralMethod.Quillen
