/-
  EPIC_018 — External validation **tranche T11**: pullback (fiber product) / sheaf gluing pattern.

  **Mathematical story:** For `f : A → C` and `g : B → C`, the pullback
  `{(a,b) : A × B // f a = g b}` is the standard **equalizer of composites** with the product;
  it matches the sheaf **intersection / compatibility** story for two partial sections over a
  common base.

  **Hypothesis:** `∀ a : A, ∃ b : B, f a = g b` so the first projection is surjective.

  **Architecture bundle:** fiber, surjectivity, `HasRightInverse`, explicit section from choice.

  Imports: `Logic.Function.Basic`, `Classical` (noncomputable section).
-/

import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

variable {A B C : Type u} (f : A → C) (g : B → C)

def PullbackType : Type u :=
  { p : A × B // f p.1 = g p.2 }

@[simp]
def pullbackFst (p : PullbackType f g) : A :=
  p.val.1

def PullbackFiber (a : A) : Type u :=
  { q : PullbackType f g // pullbackFst f g q = a }

variable (h : ∀ a : A, ∃ b : B, f a = g b)

noncomputable def pullbackSection : A → PullbackType f g := fun a =>
  ⟨(a, Classical.choose (h a)), Classical.choose_spec (h a)⟩

theorem pullbackFst_surjective (h : ∀ a : A, ∃ b : B, f a = g b) :
    Function.Surjective (pullbackFst f g) := fun a =>
  ⟨pullbackSection f g h a, rfl⟩

theorem pullbackFst_hasRightInverse (h : ∀ a : A, ∃ b : B, f a = g b) :
    Function.HasRightInverse (pullbackFst f g) :=
  Function.Surjective.hasRightInverse (pullbackFst_surjective f g h)

theorem pullbackSection_rightInverse_pullbackFst (h : ∀ a : A, ∃ b : B, f a = g b) :
    Function.RightInverse (pullbackSection f g h) (pullbackFst f g) := by
  intro a
  rfl

theorem pullback_fiber_nonempty (h : ∀ a : A, ∃ b : B, f a = g b) (a : A) :
    Nonempty (PullbackFiber f g a) :=
  ⟨⟨pullbackSection f g h a, rfl⟩⟩

noncomputable def canonicalPullbackFiberWitness (h : ∀ a : A, ∃ b : B, f a = g b) (a : A) :
    PullbackFiber f g a :=
  ⟨pullbackSection f g h a, rfl⟩

end InfinityCompression.Validation
