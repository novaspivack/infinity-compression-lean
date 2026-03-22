/-
  EPIC 009 — Non-vacuity and separation (Theorems T-9.1–T-9.6).

  Witnesses are grounded in `InfinityCompression.Core.FailureModes` (SEP-3.1/3.2) and
  polarity exclusion (EPIC 006) where cited.
-/

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.FailureModes
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Core.LocalCoherence
import InfinityCompression.Schemas.NegativeDiagonal

namespace InfinityCompression.Schemas

open InfinityCompression.Core

/-! ### T-9.1 — degenerate self-presentation (constant / non-injective contact) -/

/-- T-9.1: some `SelfPresentedFamily`s are not faithful (constant contact); hence `noFaithfulSelfPresentation`. -/
theorem faithful_spf_excludes_degenerate :
    ∃ (F : SelfPresentedFamily ℕ ℕ ℕ Bool), ¬ Function.Injective F.contact :=
  witness_no_faithful_spf

/-! ### T-9.2 — local coherence does not force global completion -/

/-- T-9.2: a faithful, locally coherent family can still admit **no** `CompletionWitness` for a fixed GRS
  (here: amalgamation obstruction on `standardBoolGRS3`). -/
theorem local_coherence_strictly_weaker_than_global :
    ∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
      (IS : InteractionStructure (Fin 3)) (LWS : LocalWitnessSpace Bool Bool),
      Nonempty (LocalCoherence F.toSPF IS LWS) ∧
        ¬ Nonempty (CompletionWitness F.toSPF standardBoolGRS3) :=
  witness_no_amalgamation

/-! ### T-9.3 — degenerate compression profiles exist -/

/-- Every `CompressionProfile` field false (trivial “compression”). -/
def degenerateCompressionProfile : CompressionProfile :=
  { hasFiniteCharacterization := False
    hasVerificationReduction := False
    hasTransferConcentration := False
    hasRepresentationEconomy := False
    hasUniformity := False }

/-- T-9.3: not every profile is the non-trivial induction profile. -/
theorem not_all_profiles_are_nontrivial :
    ∃ p : CompressionProfile,
      ¬ p.hasFiniteCharacterization ∧ ¬ p.hasVerificationReduction ∧ ¬ p.hasTransferConcentration ∧
        ¬ p.hasRepresentationEconomy ∧ ¬ p.hasUniformity :=
  ⟨degenerateCompressionProfile, by simp [degenerateCompressionProfile]⟩

/-! ### T-9.4 — coherent family with no escape (empty opposition) -/

/-- T-9.4: local coherence can hold while **no** `EscapeWitness` exists for `opposes := fun _ _ => False`. -/
theorem coherent_family_resists_escape :
    Nonempty (LocalCoherence (C := Fin 1) nv25Family.toSPF nv25Interaction nv23WitnessSpace) ∧
      ¬ Nonempty (EscapeWitness (W := Unit) nv25Family.toSPF (fun _ _ => False)) :=
  And.intro (Nonempty.intro nv25LocalCoherence)
    (fun ⟨e⟩ => sep_escape_excludes_empty_opposition nv25Family e)

/-! ### T-9.5 — anti-contact without completion (inadmissible globals) -/

/-- A `GlobalRealizationSpace` with **no** admissible globals: completion is impossible structurally. -/
def allInadmissibleGRS : GlobalRealizationSpace Bool (Fin 1) Bool where
  globLoc := fun g _ => g
  admissible := fun _ => False
  realizes := (· = ·)
  leq := fun _ _ => True
  leq_refl := fun _ => trivial
  leq_trans := fun _ _ _ _ _ => trivial

instance nv28_neq_anti : AntiContactRule nv28Family.toSPF (· ≠ ·) where
  antiDatum := not
  opposes_anti := fun v => by cases v <;> decide

instance nv28_has_repr : HasRepresentability nv28Family.toSPF (· ≠ ·) :=
  inferInstance

/-- T-9.5: `AntiContactRule` + representability can coexist with **no** `CompletionWitness` for a chosen GRS. -/
theorem anti_contact_family_resists_completion :
    ¬ Nonempty (CompletionWitness nv28Family.toSPF allInadmissibleGRS) := by
  rintro ⟨w⟩
  refine sep_completion_excludes_inadmissible nv28Family.toSPF allInadmissibleGRS (fun g hg => ?_) w
  cases hg

/-! ### T-9.6 — pairwise failure-mode separation (SEP-3.2 bundle) -/

/-- T-9.6: all 21 pairwise separation statements hold simultaneously (`Core.FailureModes`, SEP-3.2). -/
def failure_modes_pairwise_distinct :=
  InfinityCompression.Core.failure_modes_pairwise_distinct

end InfinityCompression.Schemas
