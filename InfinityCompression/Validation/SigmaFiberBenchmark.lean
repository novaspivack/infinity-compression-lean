/-
  EPIC_016_WV2B — External validation **tranche 3** (survey paper): dependent sum (bundle) projection.

  **Mathematical story:** For `E : B → Type u`, the projection `Sigma.fst : (Σ b, E b) → B`
  is the standard **bundle** forgetful map; the fiber over `b : B` is (equivalent to) the
  fiber type `E b`. This is the dependent generalization of the Cartesian product tranche.

  **Hypothesis:** `∀ b, Nonempty (E b)` so that `Sigma.fst` is surjective (every base point has
  something upstairs).

  **Architecture-guided bundle:** `SigmaFiber`, surjectivity, `HasRightInverse` from Mathlib,
  a `noncomputable` canonical section via `Classical.choose`, and `canonicalSigmaFiberWitness`.

  Imports: Mathlib `Function` + `Nonempty` + `Classical` for choice.
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nonempty

universe u

namespace InfinityCompression.Validation

variable {B : Type u} (E : B → Type u)

/-- Fiber over `b`: total points in the total space that lie over `b`. -/
def SigmaFiber (b : B) : Type u :=
  { z : Σ b' : B, E b' // Sigma.fst z = b }

theorem sigma_fiber_nonempty (h : ∀ b : B, Nonempty (E b)) (b : B) : Nonempty (SigmaFiber E b) := by
  obtain ⟨e⟩ := h b
  exact ⟨⟨⟨b, e⟩, rfl⟩⟩

theorem sigma_fst_surjective (h : ∀ b : B, Nonempty (E b)) :
    Function.Surjective (Sigma.fst : (Σ b, E b) → B) := by
  intro b
  obtain ⟨e⟩ := h b
  exact ⟨⟨b, e⟩, rfl⟩

theorem sigma_fst_hasRightInverse (h : ∀ b : B, Nonempty (E b)) :
    Function.HasRightInverse (Sigma.fst : (Σ b : B, E b) → B) :=
  Function.Surjective.hasRightInverse (sigma_fst_surjective (E := E) h)

noncomputable section
open Classical

noncomputable def chooseFiber (E : B → Type u) (h : ∀ b : B, Nonempty (E b)) (b : B) : E b :=
  Classical.choice (h b)

/-- Global section of `Sigma.fst` (right inverse in Mathlib’s `RightInverse` sense). -/
noncomputable def sigmaSection (E : B → Type u) (h : ∀ b : B, Nonempty (E b)) : B → Σ b : B, E b :=
  fun b => ⟨b, chooseFiber E h b⟩

theorem sigmaSection_rightInverse_sigma_fst (h : ∀ b : B, Nonempty (E b)) :
    Function.RightInverse (sigmaSection E h) Sigma.fst := by
  intro b
  rfl

/-- Uniform canonical witness in each `SigmaFiber` over `b`. -/
noncomputable def canonicalSigmaFiberWitness (h : ∀ b : B, Nonempty (E b)) (b : B) : SigmaFiber E b :=
  ⟨sigmaSection E h b, rfl⟩

end

end InfinityCompression.Validation
