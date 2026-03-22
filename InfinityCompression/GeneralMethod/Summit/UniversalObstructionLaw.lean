/-
  EPIC_GS1 — **Universal obstruction law** (Route B unification).

  Across domains, the same formal pattern appears: a **forgetful comparison map** is not
  injective on admissible witnesses, equivalently a **nontrivial fiber** above some bare
  certificate. At the RCA level this is `ProperExtensionViaForgetful` on `forget`; at the
  Galois level it is failure of section / nontrivial cocycle (via `EmbeddingProblem`); at the
  computability level it is failure of `ComputablePred` (halting / Rice).

  This module states the **shared combinatorial core** used everywhere: collision above a point.
-/

import InfinityCompression.MetaProof.ReflectiveRouteComparison

universe u

namespace InfinityCompression.GeneralMethod.Summit

open InfinityCompression.MetaProof

/-- Shared pattern: two distinct points in the domain with the same image (“nontrivial fiber”). -/
def ForgetfulCollision {α β : Type u} (π : α → β) : Prop :=
  ProperExtensionViaForgetful π

theorem forgetfulCollision_iff_not_injective {α β : Type u} (π : α → β) :
    ForgetfulCollision π ↔ ¬Function.Injective π := by
  classical
  refine ⟨fun ⟨x₁, x₂, hne, heq⟩ hinj => ?_, fun hni => ?_⟩
  · exact hne (hinj heq)
  · obtain ⟨x₁, x₂, heq, hne⟩ := Function.not_injective_iff.mp hni
    exact ⟨x₁, x₂, hne, heq⟩

/-- Boundary theorem (Route A): injective forgetful maps admit **no** proper extension. -/
theorem injective_implies_no_collision {α β : Type u} {π : α → β} (hinj : Function.Injective π) :
    ¬ForgetfulCollision π := fun ⟨_, _, hne, heq⟩ => hne (hinj heq)

end InfinityCompression.GeneralMethod.Summit
