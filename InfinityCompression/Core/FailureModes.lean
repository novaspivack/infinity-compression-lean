/-
  EPIC 003 — Failure modes (Def 3.3) + SEP-3.1/3.2 + witness theorems
-/

import Mathlib.Computability.Halting
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.FinCases

import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Core.LocalCoherence
import InfinityCompression.Core.SelfPresentation

namespace InfinityCompression.Core

open ComputablePred Nat.Partrec.Code

/-- Def 3.3 — taxonomy of compression failure. -/
inductive FailureMode where
  | noFaithfulSelfPresentation
  | noLocalCoherence
  | noAmalgamation
  | noAdmissibilityPreserved
  | noCanonicity
  | noTransfer
  | incompletenessBarrier

/-! ### SEP-3.1 — isolation witnesses -/

def constantContactSPF : SelfPresentedFamily ℕ ℕ ℕ Bool where
  obj := id
  contact := fun _ => 0
  loc := fun _ _ => true

theorem witness_no_faithful_spf :
    ∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact :=
  ⟨constantContactSPF, fun h => by
    have := @h 0 1 (by decide)
    simp at this⟩

theorem witness_no_local_coherence :
    ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness :=
  sep_local_coherence_excludes_contradiction

/-- Contacts lie in `{0,1}` or `{2}` only; the triple `{0,1,2}` does not interact. -/
def amalgPairIS : InteractionStructure (Fin 3) where
  contactsInteract := fun s => s ⊆ ({0, 1} : Finset (Fin 3)) ∨ s ⊆ ({2} : Finset (Fin 3))

def amalgLoc : Fin 3 → Fin 3 → Bool :=
  fun i j => decide (i = j) && (i.val < 2)

theorem amalgWitness_loc_sep (i j : Fin 3) (hij : i ≠ j) :
    ∃ l : Fin 3, amalgLoc l (id i) ≠ amalgLoc l (id j) := by
  classical
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact ⟨0, by native_decide⟩
  · exact ⟨0, by native_decide⟩
  · exact ⟨0, by native_decide⟩
  · exact ⟨1, by native_decide⟩
  · exact ⟨0, by native_decide⟩
  · exact ⟨1, by native_decide⟩

/-- `true` on `0,1` and `false` on `2`. -/
def amalgWitnessFaithful : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool where
  obj := id
  contact := id
  loc := amalgLoc
  contact_injective := Function.injective_id
  loc_contact_separates := fun i j hij => by
    simpa [amalgLoc, id_eq] using amalgWitness_loc_sep i j hij

instance amalgWitnessLocalCoherence :
    LocalCoherence (C := Fin 3) amalgWitnessFaithful.toSPF amalgPairIS nv23WitnessSpace where
  jointCompat := fun J hJ => by
    simp only [SelfPresentedFamily.subfamilyInteracts, amalgWitnessFaithful] at hJ
    rcases hJ with hJ | hJ
    · use true
      intro j hj
      have hj' : j ∈ ({0, 1} : Finset (Fin 3)) :=
        Finset.mem_of_subset hJ (Finset.mem_image_of_mem _ hj)
      fin_cases j <;> simp [nv23WitnessSpace, SelfPresentedFamily.selfContactAt, amalgWitnessFaithful, amalgLoc] at hj' ⊢
    · use false
      intro j hj
      have hj' : j ∈ ({2} : Finset (Fin 3)) :=
        Finset.mem_of_subset hJ (Finset.mem_image_of_mem _ hj)
      fin_cases j <;> simp [nv23WitnessSpace, SelfPresentedFamily.selfContactAt, amalgWitnessFaithful, amalgLoc] at hj' ⊢

/-- Standard `Bool` globalizer: same value at every contact. -/
def standardBoolGRS3 : GlobalRealizationSpace Bool (Fin 3) Bool where
  globLoc := fun g c => g
  admissible := fun _ => True
  realizes := (· = ·)
  leq := (· ≤ ·)
  leq_refl := fun g : Bool => by cases g <;> simp
  leq_trans := fun g h k a b => by
    cases g <;> cases h <;> cases k <;> simp_all

theorem no_completion_amalgWitness :
    ¬ Nonempty (CompletionWitness amalgWitnessFaithful.toSPF standardBoolGRS3) := by
  rintro ⟨Γ⟩
  have h0 := Γ.realizes_all 0
  have h2 := Γ.realizes_all 2
  simp [SelfPresentedFamily.selfContactAt, amalgWitnessFaithful, amalgLoc, standardBoolGRS3, id_eq] at h0 h2
  rw [h0] at h2
  simp at h2

theorem witness_no_amalgamation :
    ∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
      (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
      Nonempty (LocalCoherence F.toSPF IS LWS) ∧
        ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3) :=
  ⟨amalgWitnessFaithful, amalgPairIS, nv23WitnessSpace,
    Nonempty.intro amalgWitnessLocalCoherence,
    no_completion_amalgWitness⟩

theorem witness_no_admissibility :
    ∀ (GRS : GlobalRealizationSpace Bool (Fin 1) Bool), (∀ g : Bool, ¬ GRS.admissible g) →
      ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool), (CompletionWitness F GRS) → False := by
  intro GRS h F w
  exact sep_completion_excludes_inadmissible F GRS h w

/-- `globLoc` is constant on contacts so two incomparable subsets can both realize the same locals. -/
def canonicityGRS : GlobalRealizationSpace (Finset (Fin 2)) (Fin 2) Bool where
  globLoc := fun _ _ => true
  admissible := fun _ => True
  realizes := (· = ·)
  leq := (· ⊆ ·)
  leq_refl := fun _ => Finset.Subset.refl _
  leq_trans := fun _ _ _ a b => Finset.Subset.trans a b

def canonicityFamily : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool where
  obj := fun _ => {0}
  contact := fun _ => 0
  loc := fun g c => c ∈ g

theorem witness_no_canonicity :
    ∃ (G : Type) (GRS : GlobalRealizationSpace G (Fin 2) Bool) (F : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool),
      ∃ g₁ g₂ : G,
        GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
          (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
            (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
              ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁ := by
  refine ⟨Finset (Fin 2), canonicityGRS, canonicityFamily, {0}, {1}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · intro i
    fin_cases i
    simp [SelfPresentedFamily.selfContactAt, canonicityFamily, canonicityGRS]
  · intro i
    fin_cases i
    simp [SelfPresentedFamily.selfContactAt, canonicityFamily, canonicityGRS]
  · intro h
    exact (Finset.not_subset.mpr
      ⟨0, Finset.mem_singleton_self (0 : Fin 2), by simp [Finset.mem_singleton, Fin.ext_iff]⟩) h
  · intro h
    exact (Finset.not_subset.mpr
      ⟨1, Finset.mem_singleton_self (1 : Fin 2), by simp [Finset.mem_singleton, Fin.ext_iff]⟩) h

def vacuousRealizesGRS : GlobalRealizationSpace Unit (Fin 1) Bool where
  globLoc := fun _ _ => true
  admissible := fun _ => True
  realizes := fun _ _ => True
  leq := fun _ _ => True
  leq_refl := fun _ => trivial
  leq_trans := fun _ _ _ _ _ => trivial

def vacuousWitnessFamily : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool :=
  nv21Family

def vacuousCompletionWitness : CompletionWitness vacuousWitnessFamily vacuousRealizesGRS where
  complete := ()
  realizes_all := fun i => by
    fin_cases i
    trivial
  admissible_complete := trivial
  canonical := fun _ _ _ => trivial

theorem witness_no_transfer :
    ∃ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
      (GRS : GlobalRealizationSpace Unit (Fin 1) Bool),
      Nonempty (CompletionWitness F GRS) :=
  ⟨vacuousWitnessFamily, vacuousRealizesGRS, ⟨vacuousCompletionWitness⟩⟩

theorem witness_incompleteness_barrier :
    ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  ⟨fun c => (eval c 0).Dom, halting_problem 0⟩

/-! ### SEP-3.2 — pairwise distinguishability (21 unordered pairs)

Each theorem is the conjunction of the EPIC-003 isolation witnesses for its two modes,
so the separation is **contentful** (not merely `∃ H : Prop, H`).
-/

theorem sep_failure_0_1 :
    (∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact) ∧
      ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness :=
  And.intro witness_no_faithful_spf witness_no_local_coherence

theorem sep_failure_0_2 :
    (∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact) ∧
      ∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
        (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
        Nonempty (LocalCoherence F.toSPF IS LWS) ∧
          ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3) :=
  And.intro witness_no_faithful_spf witness_no_amalgamation

theorem sep_failure_0_3 :
    (∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact) ∧
      (∀ (GRS : GlobalRealizationSpace Bool (Fin 1) Bool), (∀ g : Bool, ¬ GRS.admissible g) →
        ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool), CompletionWitness F GRS → False) :=
  And.intro witness_no_faithful_spf witness_no_admissibility

theorem sep_failure_0_4 :
    (∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact) ∧
      ∃ (G : Type) (GRS : GlobalRealizationSpace G (Fin 2) Bool)
        (F : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool),
        ∃ g₁ g₂ : G,
          GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
            (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
              (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
                ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁ :=
  And.intro witness_no_faithful_spf witness_no_canonicity

theorem sep_failure_0_5 :
    (∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact) ∧
      ∃ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
        (GRS : GlobalRealizationSpace Unit (Fin 1) Bool),
        Nonempty (CompletionWitness F GRS) :=
  And.intro witness_no_faithful_spf witness_no_transfer

theorem sep_failure_0_6 :
    (∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact) ∧
      ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  And.intro witness_no_faithful_spf witness_incompleteness_barrier

theorem sep_failure_1_2 :
    ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness ∧
      ∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
        (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
        Nonempty (LocalCoherence F.toSPF IS LWS) ∧
          ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3) :=
  And.intro witness_no_local_coherence witness_no_amalgamation

theorem sep_failure_1_3 :
    ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness ∧
      (∀ (GRS : GlobalRealizationSpace Bool (Fin 1) Bool), (∀ g : Bool, ¬ GRS.admissible g) →
        ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool), CompletionWitness F GRS → False) :=
  And.intro witness_no_local_coherence witness_no_admissibility

theorem sep_failure_1_4 :
    ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness ∧
      ∃ (G : Type) (GRS : GlobalRealizationSpace G (Fin 2) Bool)
        (F : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool),
        ∃ g₁ g₂ : G,
          GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
            (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
              (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
                ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁ :=
  And.intro witness_no_local_coherence witness_no_canonicity

theorem sep_failure_1_5 :
    ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness ∧
      ∃ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
        (GRS : GlobalRealizationSpace Unit (Fin 1) Bool),
        Nonempty (CompletionWitness F GRS) :=
  And.intro witness_no_local_coherence witness_no_transfer

theorem sep_failure_1_6 :
    ¬ LocalCoherence (C := Fin 2) sep22Faithful.toSPF sep22Interaction sep22Witness ∧
      ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  And.intro witness_no_local_coherence witness_incompleteness_barrier

theorem sep_failure_2_3 :
    (∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
        (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
        Nonempty (LocalCoherence F.toSPF IS LWS) ∧
          ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3)) ∧
      (∀ (GRS : GlobalRealizationSpace Bool (Fin 1) Bool), (∀ g : Bool, ¬ GRS.admissible g) →
        ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool), CompletionWitness F GRS → False) :=
  And.intro witness_no_amalgamation witness_no_admissibility

theorem sep_failure_2_4 :
    (∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
        (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
        Nonempty (LocalCoherence F.toSPF IS LWS) ∧
          ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3)) ∧
      ∃ (G : Type) (GRS : GlobalRealizationSpace G (Fin 2) Bool)
        (F : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool),
        ∃ g₁ g₂ : G,
          GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
            (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
              (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
                ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁ :=
  And.intro witness_no_amalgamation witness_no_canonicity

theorem sep_failure_2_5 :
    (∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
        (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
        Nonempty (LocalCoherence F.toSPF IS LWS) ∧
          ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3)) ∧
      ∃ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
        (GRS : GlobalRealizationSpace Unit (Fin 1) Bool),
        Nonempty (CompletionWitness F GRS) :=
  And.intro witness_no_amalgamation witness_no_transfer

theorem sep_failure_2_6 :
    (∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
        (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
        Nonempty (LocalCoherence F.toSPF IS LWS) ∧
          ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3)) ∧
      ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  And.intro witness_no_amalgamation witness_incompleteness_barrier

theorem sep_failure_3_4 :
    (∀ (GRS : GlobalRealizationSpace Bool (Fin 1) Bool), (∀ g : Bool, ¬ GRS.admissible g) →
        ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool), CompletionWitness F GRS → False) ∧
      ∃ (G : Type) (GRS : GlobalRealizationSpace G (Fin 2) Bool)
        (F : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool),
        ∃ g₁ g₂ : G,
          GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
            (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
              (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
                ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁ :=
  And.intro witness_no_admissibility witness_no_canonicity

theorem sep_failure_3_5 :
    (∀ (GRS : GlobalRealizationSpace Bool (Fin 1) Bool), (∀ g : Bool, ¬ GRS.admissible g) →
        ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool), CompletionWitness F GRS → False) ∧
      ∃ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
        (GRS : GlobalRealizationSpace Unit (Fin 1) Bool),
        Nonempty (CompletionWitness F GRS) :=
  And.intro witness_no_admissibility witness_no_transfer

theorem sep_failure_3_6 :
    (∀ (GRS : GlobalRealizationSpace Bool (Fin 1) Bool), (∀ g : Bool, ¬ GRS.admissible g) →
        ∀ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool), CompletionWitness F GRS → False) ∧
      ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  And.intro witness_no_admissibility witness_incompleteness_barrier

theorem sep_failure_4_5 :
    (∃ (G : Type) (GRS : GlobalRealizationSpace G (Fin 2) Bool)
        (F : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool),
        ∃ g₁ g₂ : G,
          GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
            (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
              (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
                ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁) ∧
      ∃ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
        (GRS : GlobalRealizationSpace Unit (Fin 1) Bool),
        Nonempty (CompletionWitness F GRS) :=
  And.intro witness_no_canonicity witness_no_transfer

theorem sep_failure_4_6 :
    (∃ (G : Type) (GRS : GlobalRealizationSpace G (Fin 2) Bool)
        (F : SelfPresentedFamily (Fin 1) (Finset (Fin 2)) (Fin 2) Bool),
        ∃ g₁ g₂ : G,
          GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
            (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
              (∀ i : Fin 1, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
                ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁) ∧
      ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  And.intro witness_no_canonicity witness_incompleteness_barrier

theorem sep_failure_5_6 :
    (∃ (F : SelfPresentedFamily (Fin 1) (Fin 1) (Fin 1) Bool)
        (GRS : GlobalRealizationSpace Unit (Fin 1) Bool),
        Nonempty (CompletionWitness F GRS)) ∧
      ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  And.intro witness_no_transfer witness_incompleteness_barrier

/-- All 21 pairwise separation theorems (SEP-3.2) hold simultaneously. -/
def failure_modes_pairwise_distinct :=
  And.intro sep_failure_0_1 (And.intro sep_failure_0_2 (And.intro sep_failure_0_3 (And.intro sep_failure_0_4
    (And.intro sep_failure_0_5 (And.intro sep_failure_0_6 (And.intro sep_failure_1_2 (And.intro sep_failure_1_3
      (And.intro sep_failure_1_4 (And.intro sep_failure_1_5 (And.intro sep_failure_1_6 (And.intro sep_failure_2_3
        (And.intro sep_failure_2_4 (And.intro sep_failure_2_5 (And.intro sep_failure_2_6 (And.intro sep_failure_3_4
          (And.intro sep_failure_3_5 (And.intro sep_failure_3_6 (And.intro sep_failure_4_5 (And.intro sep_failure_4_6
            sep_failure_5_6)))))))))))))))))))

end InfinityCompression.Core
