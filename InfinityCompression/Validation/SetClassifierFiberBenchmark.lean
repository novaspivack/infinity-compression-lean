/-
  EPIC_018 — External validation **tranche T9**: `Set` / membership as classifier (`α → Prop`).

  **Mathematical story:** A subset `S : Set α` is the same data as its **characteristic map**
  `χ : α → Prop`, `χ x := x ∈ S`. The forgetful map `Subtype.val` from `{x // x ∈ S}` to `α`
  packages the subobject; fibers over `x` are inhabited exactly when `x ∈ S`.

  **Contrast T5:** T5 assumed `∀ a, p a` (global totality). Here `p` is `fun x => x ∈ S` and we
  record **pointwise** fiber nonemptiness on `S` only.

  Imports: `Data.Set.Defs`, `Logic.Function.Basic`.
-/

import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

variable {α : Type u} (S : Set α)

/-- Characteristic / classifying predicate for `S`. -/
@[simp]
def membershipClassifier (x : α) : Prop :=
  x ∈ S

/-- Fiber over `x` for the subtype projection (subobject over `α`). -/
def ClassifierFiber (x : α) : Type u :=
  { y : Subtype (· ∈ S) // y.val = x }

theorem classifier_fiber_nonempty_of_mem {x : α} (hx : x ∈ S) : Nonempty (ClassifierFiber S x) :=
  ⟨⟨⟨x, hx⟩, rfl⟩⟩

theorem classifier_fiber_empty_of_notMem {x : α} (hx : x ∉ S) (e : ClassifierFiber S x) : False := by
  obtain ⟨y, hy⟩ := e
  have hx' : x ∈ S := hy ▸ y.property
  exact hx hx'

theorem subtypeVal_surjectiveOn (h : ∀ x : α, x ∈ S) :
    Function.Surjective (Subtype.val : Subtype (· ∈ S) → α) := fun x => ⟨⟨x, h x⟩, rfl⟩

theorem subtypeVal_hasRightInverse (h : ∀ x : α, x ∈ S) :
    Function.HasRightInverse (Subtype.val : Subtype (· ∈ S) → α) :=
  Function.Surjective.hasRightInverse (subtypeVal_surjectiveOn S h)

def classifierSection (h : ∀ x : α, x ∈ S) : α → Subtype (· ∈ S) :=
  fun x => ⟨x, h x⟩

theorem classifierSection_rightInverse_subtypeVal (h : ∀ x : α, x ∈ S) :
    Function.RightInverse (classifierSection S h) (Subtype.val : Subtype (· ∈ S) → α) := by
  intro x
  rfl

end InfinityCompression.Validation
