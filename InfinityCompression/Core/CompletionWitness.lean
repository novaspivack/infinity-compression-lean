/-
  EPIC 002 — Completion witness (Def 2.7) + NV-2.7 + SEP-2.3
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.FinCases

import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.GlobalRealization

universe u1 u2 u3 u4 u5

namespace InfinityCompression.Core

structure CompletionWitness {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) where
  complete : G
  realizes_all :
    ∀ i : I,
      GRS.realizes (GRS.globLoc complete (F.contact i)) (F.selfContactAt i)
  admissible_complete : GRS.admissible complete
  canonical :
    ∀ g : G,
      GRS.admissible g →
        (∀ i, GRS.realizes (GRS.globLoc g (F.contact i)) (F.selfContactAt i)) →
          GRS.leq complete g

/-- Trivial singleton completion witness (EPIC 007 adds deeper mathematical examples). -/
def nv27Family : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool :=
  nv21Family

def nv27GRS : GlobalRealizationSpace Bool (Fin 1) Bool where
  globLoc := fun g c => g
  admissible := fun _ => True
  realizes := (· = ·)
  leq := (· ≤ ·)
  leq_refl := fun g : Bool => by cases g <;> simp
  leq_trans := fun g h k a b => by
    cases g <;> cases h <;> cases k <;> simp_all

def nv27Completion : CompletionWitness nv27Family nv27GRS where
  complete := true
  realizes_all := fun i => by
    fin_cases i
    simp [SelfPresentedFamily.selfContactAt, nv27Family, nv21Family, nv27GRS]
  admissible_complete := trivial
  canonical := fun g _ hreal => by
    have hg0 := hreal ⟨0, by decide⟩
    fin_cases g <;> simp [nv27GRS, SelfPresentedFamily.selfContactAt, nv27Family, nv21Family] at hg0 ⊢

theorem sep_completion_excludes_inadmissible :
    ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
      (GRS : GlobalRealizationSpace Bool (Fin 1) Bool),
      (∀ g : Bool, ¬ GRS.admissible g) → (CompletionWitness F GRS) → False := by
  intro F GRS hbad w
  exact (hbad w.complete) w.admissible_complete

example : Nonempty (CompletionWitness nv27Family nv27GRS) :=
  ⟨nv27Completion⟩

end InfinityCompression.Core
