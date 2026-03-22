/-
  EPIC 002 — Self-presented families (Def 2.1)
-/

import Mathlib.Data.Fintype.Basic

universe u1 u2 u3 u4

namespace InfinityCompression.Core

structure SelfPresentedFamily (I : Type u1) (L : Type u2) (C : Type u3) (V : Type u4) where
  obj     : I → L
  contact : I → C
  loc     : L → C → V

def SelfPresentedFamily.selfContactAt {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    (F : SelfPresentedFamily I L C V) (i : I) : V :=
  F.loc (F.obj i) (F.contact i)

/-- NV-2.1: a concrete inhabited self-presented family on `Fin 1`. -/
def nv21Family : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool where
  obj := id
  contact := id
  loc := fun _ _ => true

example : Nonempty (SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool) :=
  ⟨nv21Family⟩

end InfinityCompression.Core
