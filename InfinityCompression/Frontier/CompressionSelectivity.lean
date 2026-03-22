/-
  EPIC 018 — UL-5: compression selectivity (T-18.1).
-/

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.FailureModes
import InfinityCompression.Core.GlobalRealization

universe u1 u2 u3 u4 u5

namespace InfinityCompression.Frontier

open InfinityCompression.Core

/-- TC profile used in the program spec for T-18.1 (all gains except uniformity). -/
def tcSelectivityProfile : CompressionProfile :=
  { hasFiniteCharacterization := True
    hasVerificationReduction := True
    hasTransferConcentration := True
    hasRepresentationEconomy := True
    hasUniformity := False }

/-- T-18.1 — structurally hard family: no completion and no escape (both polarities).

  With the spec’s TC profile, `∃ _` with `hasTransferConcentration` is equivalent to
  `Nonempty` of the witness. -/
theorem compression_selectivity :
    ∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
      (GRS : GlobalRealizationSpace Bool (Fin 3) Bool)
      (opposes : Bool → Bool → Prop),
      ¬ Nonempty (CompletionWitness F.toSPF GRS) ∧
        ¬ Nonempty (EscapeWitness (W := Unit) F.toSPF opposes) :=
  ⟨amalgWitnessFaithful, standardBoolGRS3, fun _ _ => False,
    And.intro no_completion_amalgWitness fun h =>
      Nonempty.elim h (fun e => False.elim (e.opposes_all (0 : Fin 3)))⟩

/-- T-18.1 — surface form from the program spec: profile field `hasTransferConcentration` on witnesses.

  Here `hasTransferConcentration` is `True`, so each conjunct is `¬ Nonempty` of the corresponding
  witness type (same content as `compression_selectivity`). -/
theorem compression_selectivity_spec :
    ∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
      (GRS : GlobalRealizationSpace Bool (Fin 3) Bool)
      (opposes : Bool → Bool → Prop),
      ¬ (∃ _ : CompletionWitness F.toSPF GRS, tcSelectivityProfile.hasTransferConcentration) ∧
        ¬ (∃ _ : EscapeWitness (W := Unit) F.toSPF opposes, tcSelectivityProfile.hasTransferConcentration) := by
  obtain ⟨F, GRS, opposes, h⟩ := compression_selectivity
  refine ⟨F, GRS, opposes, ?_⟩
  constructor
  · intro hC
    rcases hC with ⟨w, hw⟩
    simp [tcSelectivityProfile] at hw
    exact h.1 (Nonempty.intro w)
  · intro hE
    rcases hE with ⟨e, he⟩
    simp [tcSelectivityProfile] at he
    exact h.2 (Nonempty.intro e)

end InfinityCompression.Frontier
