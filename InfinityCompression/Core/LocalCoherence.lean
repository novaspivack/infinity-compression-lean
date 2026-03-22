/-
  EPIC 002 — Local coherence (Def 2.5) + NV-2.5 + SEP-2.2
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FinCases

import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.InteractionStructure
import InfinityCompression.Core.LocalWitnessSpace

universe u1 u2 u3 u4 u5 u6

namespace InfinityCompression.Core

class LocalCoherence {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {W : Type u5}
    [DecidableEq C] (F : SelfPresentedFamily I L C V) (IS : InteractionStructure C)
    (LWS : LocalWitnessSpace V W) where
  jointCompat :
    ∀ J : Finset I,
      F.subfamilyInteracts IS J →
        ∃ w : W, ∀ j ∈ J, LWS.compatible w (F.selfContactAt j)

def nv25Interaction : InteractionStructure (Fin 1) where
  contactsInteract := fun _ => True

/-- NV-2.5: singleton family with universal interaction and equality witnesses. -/
def nv25Family : FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool where
  obj := id
  contact := id
  loc := fun _ _ => true
  contact_injective := Function.injective_id
  loc_contact_separates := fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp at hij

instance nv25LocalCoherence :
    LocalCoherence (C := Fin 1) nv25Family.toSPF nv25Interaction nv23WitnessSpace where
  jointCompat := fun J _ => by
    use nv25Family.selfContactAt ⟨0, by decide⟩
    intro j hj
    fin_cases j
    simp [nv23WitnessSpace, nv25Family]

/-- Faithful family on `Fin 2` with contradictory diagonal self-contact data. -/
def sep22Faithful : FaithfulSelfPresentation (Fin 2) (Fin 2) (Fin 2) Bool where
  obj := id
  contact := id
  loc := fun l c => decide (l = c) && decide (l = 0)
  contact_injective := Function.injective_id
  loc_contact_separates := fun i j hij => by
    classical
    refine ⟨0, ?_⟩
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> native_decide

def sep22Interaction : InteractionStructure (Fin 2) where
  contactsInteract := fun _ => True

def sep22Witness : LocalWitnessSpace Bool Bool where
  compatible := (· = ·)

theorem sep_local_coherence_excludes_contradiction :
    ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness := by
  intro h
  have hJ :=
    h.jointCompat (Finset.univ : Finset (Fin 2))
      (show sep22Faithful.toSPF.subfamilyInteracts sep22Interaction Finset.univ by
        simp [SelfPresentedFamily.subfamilyInteracts, sep22Interaction])
  rcases hJ with ⟨w, hw⟩
  have h0 := hw 0 (Finset.mem_univ _)
  have h1 := hw 1 (Finset.mem_univ _)
  simp only [SelfPresentedFamily.selfContactAt, sep22Faithful, sep22Witness] at h0 h1
  rw [h0] at h1
  cases h1

example : Nonempty (LocalCoherence (C := Fin 1) nv25Family.toSPF nv25Interaction nv23WitnessSpace) :=
  ⟨nv25LocalCoherence⟩

end InfinityCompression.Core
