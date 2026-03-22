/-
  EPIC_017 — External validation **tranche T6**: orbit equivalence quotient (group action).

  **Mathematical story:** A group `G` acts on `X`. The relation `x ~ y` iff `∃ g, g • x = y`
  is the **orbit** relation; its quotient is the orbit space.

  **Architecture bundle:** collapse / fiber / `Quotient.out` pattern as T1, with a custom
  `Setoid` from `MulAction`.

  `G` and `X` are explicit parameters so instance resolution for `MulAction` and `Quotient`
  does not get stuck on metavariables.

  Imports: `Data.Setoid`, `Algebra.Group.Action.Basic`, `Algebra.Group.Defs`.
-/

import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Defs

universe u

namespace InfinityCompression.Validation

section OrbitQuotient

variable (G : Type u) [Group G] (X : Type u) [MulAction G X]

/-- Orbit relation: `y` is in the orbit of `x`. -/
def same_orbit (x y : X) : Prop :=
  ∃ g : G, g • x = y

theorem same_orbit_refl (x : X) : same_orbit G X x x :=
  ⟨1, one_smul G x⟩

theorem same_orbit_symm {x y : X} (h : same_orbit G X x y) : same_orbit G X y x := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

theorem same_orbit_trans {x y z : X} (hxy : same_orbit G X x y) (hyz : same_orbit G X y z) :
    same_orbit G X x z := by
  obtain ⟨g, hg⟩ := hxy
  obtain ⟨h, hh⟩ := hyz
  rw [← hh, ← hg]
  exact ⟨h * g, mul_smul h g x⟩

/-- Setoid whose quotient is the orbit space. -/
def grp_action_orbit_setoid : Setoid X where
  r := same_orbit G X
  iseqv := {
    refl := same_orbit_refl G X
    symm := same_orbit_symm G X
    trans := same_orbit_trans G X
  }

abbrev BareOrbitQuotient := Quotient (grp_action_orbit_setoid G X)

@[simp]
def to_orbit_quotient (x : X) : BareOrbitQuotient G X :=
  Quotient.mk (grp_action_orbit_setoid G X) x

def OrbitQuotientFiber (q : BareOrbitQuotient G X) : Type u :=
  { x : X // to_orbit_quotient G X x = q }

theorem orbit_quotient_fiber_nonempty (q : BareOrbitQuotient G X) :
    Nonempty (OrbitQuotientFiber G X q) := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep q
  exact ⟨⟨x, hx⟩⟩

theorem to_orbit_quotient_surjective :
    Function.Surjective (to_orbit_quotient G X) := fun q => Quotient.exists_rep q

theorem to_orbit_quotient_hasRightInverse :
    Function.HasRightInverse (to_orbit_quotient G X) :=
  Function.Surjective.hasRightInverse (to_orbit_quotient_surjective G X)

theorem quotient_out_rightInverse_to_orbit_quotient :
    Function.RightInverse (Quotient.out : BareOrbitQuotient G X → X) (to_orbit_quotient G X) :=
  Quotient.out_eq

noncomputable def canonical_orbit_quotient_fiber_witness (q : BareOrbitQuotient G X) :
    OrbitQuotientFiber G X q :=
  ⟨Quotient.out q, Quotient.out_eq q⟩

theorem orbit_quotient_fiber_nonempty' (q : BareOrbitQuotient G X) :
    Nonempty (OrbitQuotientFiber G X q) :=
  Nonempty.intro (canonical_orbit_quotient_fiber_witness G X q)

end OrbitQuotient

end InfinityCompression.Validation
