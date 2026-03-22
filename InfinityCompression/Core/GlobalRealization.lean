/-
  EPIC 002 — Global realization space (Def 2.6) + NV-2.6
-/

import Mathlib.Order.Basic

universe u v w

namespace InfinityCompression.Core

structure GlobalRealizationSpace (G : Type u) (C : Type v) (V : Type w) where
  globLoc : G → C → V
  admissible : G → Prop
  realizes : V → V → Prop
  leq : G → G → Prop
  leq_refl : ∀ g, leq g g
  leq_trans : ∀ g h k, leq g h → leq h k → leq g k

/-- NV-2.6: boolean globals, equality realization, standard order. -/
def nv26GRS : GlobalRealizationSpace Bool Bool Bool where
  globLoc := fun g _ => g
  admissible := fun _ => True
  realizes := (· = ·)
  leq := (· ≤ ·)
  leq_refl := fun g : Bool => by cases g <;> simp
  leq_trans := fun g h k a b => by
    cases g <;> cases h <;> cases k <;> simp_all

example : Nonempty (GlobalRealizationSpace Bool Bool Bool) :=
  ⟨nv26GRS⟩

end InfinityCompression.Core
