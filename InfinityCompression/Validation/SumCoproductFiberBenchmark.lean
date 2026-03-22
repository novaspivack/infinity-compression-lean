/-
  EPIC_017 — External validation **tranche T4**: coproduct / sum type with discriminant collapse.

  **Mathematical story:** `Sum A B` is the type-theoretic coproduct. The map
  `forgetSumIsLeft : Sum A B → Bool` forgets *which side* (after tagging with `inl` / `inr`).
  This is the dual flavor to the product projection tranche: **tags** instead of a Cartesian
  coordinate. Multi-route: many `inl a₁`, `inl a₂` share the same bare `true`.

  **Baseline:** both sides inhabited to hit both booleans.

  **Architecture bundle:** `SumFiberAt`, surjectivity, `HasRightInverse`, explicit section,
  canonical witnesses — same template as T2/T3.

  Imports: `Mathlib.Logic.Function.Basic` only.
-/

import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

variable {A B : Type u}

/-- Collapse `Sum A B` to a bare `Bool` (“which side”). -/
@[simp]
def forgetSumIsLeft : Sum A B → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- Fiber over a tag: `Sum` points that project to that `Bool` (`A` and `B` explicit). -/
def SumFiberAt (A B : Type u) (b : Bool) : Type u :=
  { s : Sum A B // forgetSumIsLeft s = b }

/-- Section at fixed witnesses on each side. -/
def sumSection (a0 : A) (b0 : B) : Bool → Sum A B
  | true => Sum.inl a0
  | false => Sum.inr b0

theorem sum_fiber_nonempty (a0 : A) (b0 : B) (b : Bool) : Nonempty (SumFiberAt A B b) := by
  cases b
  · exact ⟨⟨Sum.inr b0, rfl⟩⟩
  · exact ⟨⟨Sum.inl a0, rfl⟩⟩

theorem forgetSumIsLeft_surjective (a0 : A) (b0 : B) :
    Function.Surjective (forgetSumIsLeft : Sum A B → Bool) := fun b =>
  match b with
  | true => ⟨Sum.inl a0, rfl⟩
  | false => ⟨Sum.inr b0, rfl⟩

theorem forgetSumIsLeft_hasRightInverse (a0 : A) (b0 : B) :
    Function.HasRightInverse (forgetSumIsLeft : Sum A B → Bool) :=
  Function.Surjective.hasRightInverse (forgetSumIsLeft_surjective a0 b0)

theorem sumSection_rightInverse_forgetSumIsLeft (a0 : A) (b0 : B) :
    Function.RightInverse (sumSection a0 b0) forgetSumIsLeft := by
  intro b
  cases b <;> rfl

def canonicalSumFiberWitness (a0 : A) (b0 : B) (b : Bool) : SumFiberAt A B b :=
  match b with
  | true => ⟨Sum.inl a0, rfl⟩
  | false => ⟨Sum.inr b0, rfl⟩

theorem sum_fiber_nonempty' (a0 : A) (b0 : B) (b : Bool) : Nonempty (SumFiberAt A B b) :=
  Nonempty.intro (canonicalSumFiberWitness a0 b0 b)

end InfinityCompression.Validation
