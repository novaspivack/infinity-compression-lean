/-
  EPIC_018 — External validation **tranche T8**: pushout / colimit (coproduct glueing, minimal case).

  **Mathematical story:** The pushout of `A ← Unit → B` identifies one point `a0 : A` with
  `b0 : B` inside `Sum A B`. We realize the equivalence as **`EqvGen`** of the symmetric
  generating relation ( Mathlib’s standard “smallest equivalence containing these edges”).

  **Architecture bundle:** `Quotient.mk`, fibers, `Quotient.out`, same Program W spine as T1.

  Imports: `Logic.Relation` (`EqvGen.setoid`), `Data.Setoid`, `Data.Sum.Basic`.
-/

import Mathlib.Logic.Relation
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Sum.Basic

universe u

namespace InfinityCompression.Validation

open Relation

variable {A B : Type u} (a0 : A) (b0 : B)

/-- Generating edges for glueing `inl a0` to `inr b0`. -/
def pushoutRel (x y : Sum A B) : Prop :=
  (x = Sum.inl a0 ∧ y = Sum.inr b0) ∨ (x = Sum.inr b0 ∧ y = Sum.inl a0)

def pushoutSetoid : Setoid (Sum A B) :=
  EqvGen.setoid (pushoutRel a0 b0)

abbrev BarePushout := Quotient (pushoutSetoid a0 b0)

@[simp]
def forgetToPushout (x : Sum A B) : BarePushout a0 b0 :=
  Quotient.mk (pushoutSetoid a0 b0) x

def PushoutFiber (q : BarePushout a0 b0) : Type u :=
  { x : Sum A B // forgetToPushout a0 b0 x = q }

theorem pushout_fiber_nonempty (q : BarePushout a0 b0) : Nonempty (PushoutFiber a0 b0 q) := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep q
  exact ⟨⟨x, hx⟩⟩

theorem forgetToPushout_surjective :
    Function.Surjective (forgetToPushout a0 b0) := fun q => Quotient.exists_rep q

theorem forgetToPushout_hasRightInverse :
    Function.HasRightInverse (forgetToPushout a0 b0) :=
  Function.Surjective.hasRightInverse (forgetToPushout_surjective a0 b0)

theorem quotientOut_rightInverse_forgetToPushout :
    Function.RightInverse (Quotient.out : BarePushout a0 b0 → Sum A B) (forgetToPushout a0 b0) :=
  Quotient.out_eq

noncomputable def canonicalPushoutFiberWitness (q : BarePushout a0 b0) :
    PushoutFiber a0 b0 q :=
  ⟨Quotient.out q, Quotient.out_eq q⟩

theorem pushout_fiber_nonempty' (q : BarePushout a0 b0) :
    Nonempty (PushoutFiber a0 b0 q) :=
  Nonempty.intro (canonicalPushoutFiberWitness a0 b0 q)

end InfinityCompression.Validation
