/-
  EPIC 002 — Completion operator class (Def 2.9) + NV-2.9
-/

import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.SelfPresentation

universe u1 u2 u3 u4 u5 uF

namespace InfinityCompression.Core

structure CompletionOperatorClass {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (Fam : Type uF) (toSPF : Fam → SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) where
  complete : ∀ F : Fam, CompletionWitness (toSPF F) GRS
  monotone :
    ∀ F₁ F₂ : Fam,
      (∀ i, (toSPF F₁).selfContactAt i = (toSPF F₂).selfContactAt i) →
        (complete F₁).complete = (complete F₂).complete

/-- Singleton family class with constant completion at `true`. -/
inductive SingletonFam where
  | only

def singletonToSPF : SingletonFam → SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool
  | SingletonFam.only => nv27Family

def nv29Op : CompletionOperatorClass SingletonFam singletonToSPF nv27GRS where
  complete
  | SingletonFam.only => nv27Completion
  monotone := fun F₁ F₂ h => by
    cases F₁ <;> cases F₂
    rfl

example : Nonempty (CompletionOperatorClass SingletonFam singletonToSPF nv27GRS) :=
  ⟨nv29Op⟩

end InfinityCompression.Core
