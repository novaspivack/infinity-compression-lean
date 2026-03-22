/-
  EPIC 002 — Local witness space (Def 2.3) + NV-2.3
-/

universe u v

namespace InfinityCompression.Core

structure LocalWitnessSpace (V : Type u) (W : Type v) where
  compatible : W → V → Prop

/-- NV-2.3: equality as compatibility on `Bool`. -/
def nv23WitnessSpace : LocalWitnessSpace Bool Bool where
  compatible := (· = ·)

example : Nonempty (LocalWitnessSpace Bool Bool) :=
  ⟨nv23WitnessSpace⟩

end InfinityCompression.Core
