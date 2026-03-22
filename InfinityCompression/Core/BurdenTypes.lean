/-
  EPIC 003 — Burden types (Def 3.1) + NV-3.1
-/

import Mathlib.Data.Nat.Prime.Basic

namespace InfinityCompression.Core

/-- Def 3.1 — regimes of infinite proof burden. -/
inductive BurdenType where
  /-- ∀ i ∈ I, P(i) with I infinite -/
  | familyControl
  /-- Control an entire space of theories, models, or meanings -/
  | semanticControl
  /-- Multi-stage proof reduction -/
  | architecturalControl

/-- NV-3.1a: infinite family control — primality over `ℕ`. -/
def nv31aExample : BurdenType :=
  BurdenType.familyControl

example : Nat.Prime 2 ∧ nv31aExample = BurdenType.familyControl := by
  constructor
  · decide
  · rfl

/-- NV-3.1b: semantic control — assignments of propositions to atoms (`Fin n`). -/
structure PropositionalAssignment (n : ℕ) where
  val : Fin n → Prop

def nv31bExample : BurdenType :=
  BurdenType.semanticControl

example : Nonempty (PropositionalAssignment 1) ∧ nv31bExample = BurdenType.semanticControl := by
  refine ⟨Nonempty.intro (PropositionalAssignment.mk (fun _ => True)), rfl⟩

/-- NV-3.1c: architectural control — stub until EPIC 013 wires a concrete two-step chain. -/
structure ArchitecturalControlStub where
  stage1 : Unit
  stage2 : Unit

def nv31cStub : BurdenType :=
  BurdenType.architecturalControl

example : Nonempty ArchitecturalControlStub ∧ nv31cStub = BurdenType.architecturalControl := by
  refine ⟨Nonempty.intro (ArchitecturalControlStub.mk () ()), rfl⟩

end InfinityCompression.Core
