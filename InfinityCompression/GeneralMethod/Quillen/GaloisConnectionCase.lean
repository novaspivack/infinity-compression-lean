/-
  EPIC_022_OP1 — Quillen's Theorem A for Galois connections (algebraic core).

  Genuine theorems: fiber maximum, idempotence, order-isomorphic images.
  Zero sorry.
-/

import Mathlib.Order.GaloisConnection.Defs

universe u v

namespace InfinityCompression.GeneralMethod.Quillen

section GCQuillen

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
variable {l : P → Q} {u : Q → P}

/-! ### Fiber maximum -/

theorem gc_fiber_has_max (gc : GaloisConnection l u) (q : Q) (p : P) (hp : l p ≤ q) :
    p ≤ u q :=
  (gc p q).mp hp

theorem gc_uq_in_fiber (gc : GaloisConnection l u) (q : Q) : l (u q) ≤ q :=
  gc.l_u_le q

/-! ### Closure and kernel -/

theorem gc_closure (gc : GaloisConnection l u) (p : P) : p ≤ u (l p) :=
  gc.le_u_l p

theorem gc_kernel (gc : GaloisConnection l u) (q : Q) : l (u q) ≤ q :=
  gc.l_u_le q

/-! ### Idempotence -/

theorem gc_lul_eq_l (gc : GaloisConnection l u) (p : P) : l (u (l p)) = l p :=
  le_antisymm (gc.l_u_le (l p)) (gc.monotone_l (gc.le_u_l p))

theorem gc_ulu_eq_u (gc : GaloisConnection l u) (q : Q) : u (l (u q)) = u q :=
  gc.u_l_u_eq_u q

/-! ### Closed and open elements -/

def ClosedElements (l : P → Q) (u : Q → P) : Set P := { p | u (l p) = p }
def OpenElements (l : P → Q) (u : Q → P) : Set Q := { q | l (u q) = q }

theorem u_range_eq_closed (gc : GaloisConnection l u) :
    Set.range u = ClosedElements l u := by
  ext p; constructor
  · rintro ⟨q, rfl⟩; exact gc_ulu_eq_u gc q
  · intro (hp : u (l p) = p); exact ⟨l p, hp⟩

theorem l_range_eq_open (gc : GaloisConnection l u) :
    Set.range l = OpenElements l u := by
  ext q; constructor
  · rintro ⟨p, rfl⟩; exact gc_lul_eq_l gc p
  · intro (hq : l (u q) = q); exact ⟨u q, hq⟩

/-! ### l and u restrict to inverse maps -/

omit [PartialOrder P] [PartialOrder Q] in
theorem l_u_on_open (q : Q) (hq : q ∈ OpenElements l u) : l (u q) = q := hq

omit [PartialOrder P] [PartialOrder Q] in
theorem u_l_on_closed (p : P) (hp : p ∈ ClosedElements l u) : u (l p) = p := hp

theorem l_maps_closed_to_open (gc : GaloisConnection l u) (p : P)
    (_ : p ∈ ClosedElements l u) : l p ∈ OpenElements l u :=
  gc_lul_eq_l gc p

theorem u_maps_open_to_closed (gc : GaloisConnection l u) (q : Q)
    (_ : q ∈ OpenElements l u) : u q ∈ ClosedElements l u :=
  gc_ulu_eq_u gc q

/-! ### Monotonicity -/

theorem gc_l_monotone (gc : GaloisConnection l u) : Monotone l := gc.monotone_l
theorem gc_u_monotone (gc : GaloisConnection l u) : Monotone u := gc.monotone_u

end GCQuillen

/-! ### Quillen's Theorem A: what this proves and what it implies

  **Proved (zero sorry):**
  1. Every fiber `{p | l p ≤ q}` has maximum `u q` (`gc_fiber_has_max`).
  2. `u ∘ l` is idempotent on P; `l ∘ u` is idempotent on Q.
  3. Images of `l` and `u` are in order-preserving bijection.
  4. Closure inequality `id ≤ u ∘ l`; kernel inequality `l ∘ u ≤ id`.

  **Classical consequence (Quillen's Theorem A):**
  A poset fiber with a maximum has contractible order complex (cone on max).
  Therefore every fiber of `l` is contractible. By Quillen's Theorem A,
  `l` induces a homotopy equivalence on order complexes.

  **Gap:** Order complex construction + "cone is contractible" as formal lemmas.
-/

end InfinityCompression.GeneralMethod.Quillen
