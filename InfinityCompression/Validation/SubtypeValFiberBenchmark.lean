/-
  EPIC_017 — External validation **tranche T5**: subtype inclusion as forgetful map.

  **Mathematical story:** For `p : α → Prop`, `Subtype.val : Subtype p → α` forgets the proof,
  projecting to the ambient type. Fibers over `a : α` are singletons when `p a` holds (the
  canonical enriched point is `⟨a, h⟩`). This isolates the **subtype / refinement** pattern
  orthogonal to quotients and products.

  **Hypothesis:** `∀ a, p a` so that `Subtype.val` is surjective onto `α`.

  **Architecture bundle:** `SubtypeFiberAt`, surjectivity, `HasRightInverse`, section
  `fun a => ⟨a, h a⟩`, canonical witnesses.

  Imports: `Mathlib.Logic.Function.Basic` only.
-/

import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

variable {α : Type u} {p : α → Prop}

/-- Fiber over `a : α`: subtypes that project to `a` (subsingleton when `p a`). -/
def SubtypeFiberAt (a : α) : Type u :=
  { x : Subtype p // x.val = a }

theorem subtype_fiber_nonempty (h : ∀ a : α, p a) (a : α) : Nonempty (SubtypeFiberAt (p := p) a) :=
  ⟨⟨⟨a, h a⟩, rfl⟩⟩

def subtypeSection (h : ∀ a : α, p a) : α → Subtype p :=
  fun a => ⟨a, h a⟩

theorem subtype_val_surjective (h : ∀ a : α, p a) :
    Function.Surjective (Subtype.val : Subtype p → α) := fun a => ⟨⟨a, h a⟩, rfl⟩

theorem subtype_val_hasRightInverse (h : ∀ a : α, p a) :
    Function.HasRightInverse (Subtype.val : Subtype p → α) :=
  Function.Surjective.hasRightInverse (subtype_val_surjective h)

theorem subtypeSection_rightInverse_subtypeVal (h : ∀ a : α, p a) :
    Function.RightInverse (subtypeSection h) (Subtype.val : Subtype p → α) := by
  intro a
  rfl

def canonicalSubtypeFiberWitness (h : ∀ a : α, p a) (a : α) : SubtypeFiberAt (p := p) a :=
  ⟨⟨a, h a⟩, rfl⟩

theorem subtype_fiber_nonempty' (h : ∀ a : α, p a) (a : α) :
    Nonempty (SubtypeFiberAt (p := p) a) :=
  Nonempty.intro (canonicalSubtypeFiberWitness h a)

end InfinityCompression.Validation
