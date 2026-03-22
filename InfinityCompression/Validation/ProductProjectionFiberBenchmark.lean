/-
  EPIC_016_WV2B — External validation **tranche 2** (survey paper): Cartesian product projection.

  **Mathematical story:** The first projection `Prod.fst : X × Y → X` forgets the second
  coordinate. Many enriched pairs `(x, y₁)` and `(x, y₂)` share the same bare image `x`
  — a clean **multi-route over one bare certificate** without quotienting.

  **Baseline:** trivial existence of pairs over each `x` once `Y` is nonempty (pointwise).

  **Architecture-guided bundle:** named `ProductFiber`, surjectivity of `forgetFirst`,
  `HasRightInverse`, an explicit parametric section `(x ↦ (x, y₀))` as `RightInverse`, and a
  canonical fiber witness `(x, y₀)` — matching the collapse / fiber / section template.

  Imports only Mathlib lemmas for `Function` infrastructure; no IC spine.
-/

import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

/-- Forgetful map: first projection. -/
@[simp]
def forgetFirst {X Y : Type u} (p : X × Y) : X :=
  p.1

/-- Fiber over a bare point: pairs that project to it (`Y` is explicit because it is not
determined by `x : X` alone). -/
def ProductFiberAt (X Y : Type u) (x : X) : Type u :=
  { p : X × Y // forgetFirst p = x }

/-- Canonical section at a fixed second coordinate. -/
def productSection {X Y : Type u} (y0 : Y) : X → X × Y :=
  fun x => (x, y0)

/-- Every bare point has a nonempty fiber (explicit witness). -/
theorem product_fiber_nonempty {X Y : Type u} (y0 : Y) (x : X) : Nonempty (ProductFiberAt X Y x) :=
  ⟨⟨(x, y0), rfl⟩⟩

/-- `forgetFirst` is surjective onto `X` (given we can supply a second coordinate). -/
theorem forgetFirst_surjective {X Y : Type u} (y0 : Y) :
    Function.Surjective (forgetFirst : X × Y → X) :=
  fun x => ⟨(x, y0), rfl⟩

theorem forgetFirst_hasRightInverse {X Y : Type u} (y0 : Y) :
    Function.HasRightInverse (forgetFirst : X × Y → X) :=
  Function.Surjective.hasRightInverse (forgetFirst_surjective y0)

/-- Mathlib: `RightInverse f g` means `g ∘ f = id` on the domain of `f`, i.e.\ `∀ x, g (f x) = x`.
Here `f = productSection y0`, `g = forgetFirst`. -/
theorem productSection_rightInverse_forgetFirst {X Y : Type u} (y0 : Y) :
    Function.RightInverse (productSection y0 : X → X × Y) (forgetFirst : X × Y → X) := by
  intro x
  rfl

/-- Distinguished point in each fiber, coherent with the section. -/
def canonicalProductFiberWitness {X Y : Type u} (y0 : Y) (x : X) : ProductFiberAt X Y x :=
  ⟨(x, y0), rfl⟩

theorem product_fiber_nonempty' {X Y : Type u} (y0 : Y) (x : X) : Nonempty (ProductFiberAt X Y x) :=
  Nonempty.intro (canonicalProductFiberWitness y0 x)

end InfinityCompression.Validation
