/-
  EPIC 018 — UL-6: polarity balance (T-18.2) + failure mode diagnostic (T-18.3).

  T-18.2: EPIC 006 requires contact alignment for simultaneous witnesses; we include it here
  (the program spec’s bare `hExcl` is insufficient without alignment).
-/

import Mathlib.Computability.Halting

import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.FailureModes
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Core.InteractionStructure
import InfinityCompression.Core.LocalCoherence
import InfinityCompression.Core.LocalWitnessSpace
import InfinityCompression.Schemas.PolarityExclusion

universe u1 u2 u3 u4 u5

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Schemas

structure CompletionWitnessProfiled {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) where
  base : CompletionWitness F GRS
  profile : CompressionProfile

structure EscapeWitnessProfiled {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    (F : SelfPresentedFamily I L C V) (opposes : V → V → Prop) where
  base : EscapeWitness (W := Unit) F opposes
  profile : CompressionProfile

/-- T-18.2 — profile-level balance under the EPIC 006 alignment hypothesis. -/
theorem polarity_balance
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    [Inhabited I]
    (F : FaithfulSelfPresentation I L C V)
    (GRS : GlobalRealizationSpace G C V)
    (opposes : V → V → Prop)
    (hΓ : CompletionWitnessProfiled F.toSPF GRS)
    (hΔ : EscapeWitnessProfiled F.toSPF opposes)
    (hAlign :
      ∀ i : I,
        GRS.globLoc hΓ.base.complete (F.toSPF.contact i) =
          hΔ.base.escLoc hΔ.base.escape (F.toSPF.contact i))
    (hExcl : ∀ v w : V, GRS.realizes v w → opposes v w → False) :
    ¬ (hΓ.profile.hasTransferConcentration ∧ hΔ.profile.hasTransferConcentration) := fun
  ⟨_, _⟩ => polarity_exclusion hΓ.base hΔ.base hAlign hExcl

open ComputablePred Nat.Partrec.Code

/-- Predicate: which failure mode is exhibited (EPIC 003 taxonomy — all seven modes). -/
def ExhibitsMode {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    [DecidableEq C] (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V)
    (m : FailureMode) : Prop :=
  match m with
  | FailureMode.noFaithfulSelfPresentation => ¬ Function.Injective F.contact
  | FailureMode.noLocalCoherence =>
      ∃ (W : Type) (IS : InteractionStructure C) (LWS : LocalWitnessSpace V W),
        ¬ Nonempty (LocalCoherence F IS LWS)
  | FailureMode.noAmalgamation => ¬ Nonempty (CompletionWitness F GRS)
  | FailureMode.noAdmissibilityPreserved => ∀ g : G, ¬ GRS.admissible g
  | FailureMode.noCanonicity =>
      ∃ g₁ g₂ : G,
        GRS.admissible g₁ ∧ GRS.admissible g₂ ∧
          (∀ i : I, GRS.realizes (GRS.globLoc g₁ (F.contact i)) (F.selfContactAt i)) ∧
            (∀ i : I, GRS.realizes (GRS.globLoc g₂ (F.contact i)) (F.selfContactAt i)) ∧
              ¬ GRS.leq g₁ g₂ ∧ ¬ GRS.leq g₂ g₁
  | FailureMode.noTransfer => Nonempty (CompletionWitness F GRS)
  | FailureMode.incompletenessBarrier => ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p

lemma not_exists_completionWitness_true_iff_not_nonempty {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    {G : Type u5} (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) :
    (¬ ∃ _ : CompletionWitness F GRS, True) ↔ ¬ Nonempty (CompletionWitness F GRS) := by
  constructor
  · intro h hn
    rcases hn with ⟨w⟩
    exact h ⟨w, trivial⟩
  · intro h ⟨w, _⟩
    exact h (Nonempty.intro w)

/-- T-18.3 — if completion fails, amalgamation obstruction diagnoses the failure. -/
theorem failure_mode_exhaustive
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    [DecidableEq C] (F : SelfPresentedFamily I L C V)
    (GRS : GlobalRealizationSpace G C V)
    (h : ¬ Nonempty (CompletionWitness F GRS)) :
    ∃ mode : FailureMode, ExhibitsMode F GRS mode :=
  ⟨FailureMode.noAmalgamation, by simpa [ExhibitsMode] using h⟩

/-- T-18.3 — program-spec form: `¬ ∃ _ : CompletionWitness, True` (empty completion class). -/
theorem failure_mode_exhaustive_spec
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    [DecidableEq C] (F : SelfPresentedFamily I L C V)
    (GRS : GlobalRealizationSpace G C V)
    (h : ¬ ∃ _ : CompletionWitness F GRS, True) :
    ∃ mode : FailureMode, ExhibitsMode F GRS mode :=
  failure_mode_exhaustive F GRS ((not_exists_completionWitness_true_iff_not_nonempty F GRS).mp h)

end InfinityCompression.Frontier
