/-
  EPIC_017 — External validation **tranche T7**: commutative ring quotient by an ideal.

  **Mathematical story:** `Ideal.Quotient.mk I : R → R ⧸ I` collapses modulo `I` — standard
  **algebraic** quotient parallel to T1’s setoid quotient.

  **Architecture bundle:** fiber, surjectivity of `mk`, `HasRightInverse`, `Quotient.out`,
  canonical witness.

  Imports: `RingTheory.Ideal.Quotient.Defs`, `Logic.Function.Basic`.
-/

import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

variable {R : Type u} [CommRing R] (I : Ideal R)

@[simp]
def forgetToIdealQuotient (r : R) : R ⧸ I :=
  Ideal.Quotient.mk I r

def IdealQuotientFiber (q : R ⧸ I) : Type u :=
  { r : R // forgetToIdealQuotient I r = q }

theorem ideal_quotient_fiber_nonempty (q : R ⧸ I) : Nonempty (IdealQuotientFiber I q) := by
  obtain ⟨r, hr⟩ := Quotient.exists_rep q
  exact ⟨⟨r, hr⟩⟩

theorem forgetToIdealQuotient_surjective :
    Function.Surjective (forgetToIdealQuotient I) := fun q => Quotient.exists_rep q

theorem forgetToIdealQuotient_hasRightInverse :
    Function.HasRightInverse (forgetToIdealQuotient I) :=
  Function.Surjective.hasRightInverse (forgetToIdealQuotient_surjective I)

theorem idealQuotientOut_rightInverse_forgetToIdealQuotient :
    Function.RightInverse (Quotient.out : R ⧸ I → R) (forgetToIdealQuotient I) :=
  Quotient.out_eq

noncomputable def canonicalIdealQuotientFiberWitness (q : R ⧸ I) : IdealQuotientFiber I q :=
  ⟨Quotient.out q, Quotient.out_eq q⟩

theorem ideal_quotient_fiber_nonempty' (q : R ⧸ I) : Nonempty (IdealQuotientFiber I q) :=
  Nonempty.intro (canonicalIdealQuotientFiberWitness I q)

end InfinityCompression.Validation
