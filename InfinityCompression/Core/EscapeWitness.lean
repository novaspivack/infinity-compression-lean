/-
  EPIC 002 — Escape witness (Def 2.8) + NV-2.8 + SEP-2.4
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

import InfinityCompression.Core.FaithfulSelfPresentation

universe u1 u2 u3 u4 u5

namespace InfinityCompression.Core

structure EscapeWitness {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {W : Type u5}
    (F : SelfPresentedFamily I L C V) (opposes : V → V → Prop) where
  escape : W
  escLoc : W → C → V
  opposes_all : ∀ i : I, opposes (escLoc escape (F.contact i)) (F.selfContactAt i)

/-- Minimal escape witness on `Fin 1` with `Bool` inequality as opposition. -/
def nv28Family : FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool where
  obj := id
  contact := id
  loc := fun _ _ => true
  contact_injective := Function.injective_id
  loc_contact_separates := fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp at hij

def nv28Escape : EscapeWitness (W := Unit) nv28Family.toSPF (· ≠ ·) where
  escape := ()
  escLoc := fun _ _ => false
  opposes_all := fun i => by
    fin_cases i
    simp [SelfPresentedFamily.selfContactAt, nv28Family]

theorem sep_escape_excludes_empty_opposition :
    ∀ (F : FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool),
      (EscapeWitness (W := Unit) F.toSPF fun _ _ => False) → False := by
  intro F e
  exact e.opposes_all 0

example : Nonempty (EscapeWitness (W := Unit) nv28Family.toSPF (· ≠ ·)) :=
  ⟨nv28Escape⟩

end InfinityCompression.Core
