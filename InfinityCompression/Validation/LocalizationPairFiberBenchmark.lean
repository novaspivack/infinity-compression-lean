/-
  EPIC_018 — External validation **tranche T10**: commutative ring localization via fraction pairs.

  **Mathematical story:** For `[IsLocalization M S]`, every element of `S` is a fraction
  `mk' x y` with `(x, y) : R × M`. The **collapse** is not `algebraMap R S` (typically not
  surjective), but the **pair map** `(x, y) ↦ mk' x y`, which *is* surjective
  (`IsLocalization.mk'_surjective`).

  **Architecture bundle:** surjectivity from `R × M`, `HasRightInverse`, Mathlib’s
  `IsLocalization.sec` as a **RightInverse** of the pair map.

  Imports: `RingTheory.Localization.Basic`, `Logic.Function.Basic`.
-/

import Mathlib.RingTheory.Localization.Basic
import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

variable {R : Type u} [CommRing R] (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S]
  [IsLocalization M S]

noncomputable def forgetPairToLocalization (p : R × M) : S :=
  IsLocalization.mk' S p.1 p.2

theorem forgetPairToLocalization_surjective :
    Function.Surjective (forgetPairToLocalization M S) :=
  IsLocalization.mk'_surjective M

theorem forgetPairToLocalization_hasRightInverse :
    Function.HasRightInverse (forgetPairToLocalization M S) :=
  Function.Surjective.hasRightInverse (forgetPairToLocalization_surjective M S)

/-- Mathlib’s canonical pair section is a right inverse of the fraction map. -/
theorem sec_rightInverse_forgetPairToLocalization :
    Function.RightInverse (IsLocalization.sec M) (forgetPairToLocalization M S) := by
  intro z
  simp [forgetPairToLocalization, IsLocalization.mk'_sec]

def LocalizationPairFiber (z : S) : Type u :=
  { p : R × M // forgetPairToLocalization M S p = z }

theorem localization_pair_fiber_nonempty (z : S) : Nonempty (LocalizationPairFiber M S z) := by
  obtain ⟨p, hp⟩ := forgetPairToLocalization_surjective M S z
  exact ⟨⟨p, hp⟩⟩

noncomputable def canonicalLocalizationPairFiberWitness (z : S) : LocalizationPairFiber M S z :=
  ⟨IsLocalization.sec M z, by simp [forgetPairToLocalization, IsLocalization.mk'_sec]⟩

end InfinityCompression.Validation
