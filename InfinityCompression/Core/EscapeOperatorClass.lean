/-
  EPIC 002 — Escape operator class (Def 2.10) + NV-2.10
-/

import Mathlib.Tactic.FinCases

import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.SelfPresentation

universe u1 u2 u3 u4 u5 uF

namespace InfinityCompression.Core

structure EscapeOperatorClass {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} (W : Type u5)
    (Fam : Type uF) (toSPF : Fam → SelfPresentedFamily I L C V) (opposes : V → V → Prop) where
  escape : ∀ F : Fam, EscapeWitness (W := W) (toSPF F) opposes
  uniform :
    ∀ F₁ F₂ : Fam,
      (∀ i, (toSPF F₁).selfContactAt i = (toSPF F₂).selfContactAt i) →
        (escape F₁).escape = (escape F₂).escape

/-- Two labels for the same `Fin 2` SPF so `uniform` is nontrivial. -/
inductive BoolFunFam where
  | a | b

def boolFunToSPF : BoolFunFam → SelfPresentedFamily (Fin 2) Bool Bool Bool
  | BoolFunFam.a | BoolFunFam.b =>
      { obj := fun _ => true
        contact := fun _ => true
        loc := fun l c => l && c }

def diagonalOpposes : Bool → Bool → Prop :=
  (· ≠ ·)

def nv210EscapeOp : EscapeOperatorClass Unit BoolFunFam boolFunToSPF diagonalOpposes where
  escape
  | BoolFunFam.a =>
      { escape := ()
        escLoc := fun _ _ => false
        opposes_all := fun i => by
          fin_cases i <;> simp [SelfPresentedFamily.selfContactAt, boolFunToSPF, diagonalOpposes] }
  | BoolFunFam.b =>
      { escape := ()
        escLoc := fun _ _ => false
        opposes_all := fun i => by
          fin_cases i <;> simp [SelfPresentedFamily.selfContactAt, boolFunToSPF, diagonalOpposes] }
  uniform := fun F₁ F₂ _ => by
    cases F₁ <;> cases F₂ <;> rfl

example : Nonempty (EscapeOperatorClass Unit BoolFunFam boolFunToSPF diagonalOpposes) :=
  ⟨nv210EscapeOp⟩

end InfinityCompression.Core
