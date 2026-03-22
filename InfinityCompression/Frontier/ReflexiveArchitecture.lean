/-
  EPIC 016 — Reflexive Architecture Theorem (crown): NEMS spine as meta self-presentation
  + non-trivial profile + EPIC 012 limit corollary.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.FailureModes
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Meta.CompressionArchitecture
import InfinityCompression.Meta.CompressionInstance
import InfinityCompression.Meta.NEMSSpineAsArchitecture
import InfinityCompression.Bridges.NoFinalSelfTheoryAsLimit

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Meta
open InfinityCompression.Bridges
open ComputablePred Nat.Partrec.Code

/-- Faithful `Fin 5`-indexed presentation used as the meta spine carrier (contact = id). -/
def nemsMetaFaithful : FaithfulSelfPresentation (Fin 5) (Fin 5) (Fin 5) (Fin 5) where
  obj := id
  contact := id
  loc := fun l c => c
  contact_injective := Function.injective_id
  loc_contact_separates := fun i j hij => by
    classical
    refine ⟨i, ?_⟩
    intro h_eq
    have hij' : i = j := by
      simpa [SelfPresentedFamily.selfContactAt, id_eq] using h_eq
    exact hij hij'

/-- Theorem 16.1 (structural): the formalized NEMS spine architecture exists and the
  meta carrier `SelfPresentedFamily` is inhabited at `Fin 5`. -/
theorem reflexive_architecture_thesis :
    (∃ _ : CompressionArchitecture Unit nemsSpineChain.steps.length, True) ∧
      Nonempty (SelfPresentedFamily (Fin 5) (Fin 5) (Fin 5) (Fin 5)) :=
  ⟨⟨nemsSpineChain.toArchitecture, trivial⟩, ⟨nemsMetaFaithful.toSPF⟩⟩

/-- Non-trivial compression at the meta level: the spine uses `nv32InductionProfile`. -/
theorem reflexive_architecture_nontrivial_profile :
    ∃ p : CompressionProfile, p.hasTransferConcentration :=
  ⟨nv32InductionProfile, trivial⟩

/-- Corollary (EPIC 012): limit pole still carries representation economy — recognition
  cannot be a total positive closure. -/
theorem reflexive_architecture_limit_corollary :
    ∃ i : CompressionInstance Unit,
      i.polarity = CompressionPolarity.limit ∧ i.profile.hasRepresentationEconomy :=
  internalization_not_totalization_is_compression_limit

/-- Level-4 companion bundle (§7 Level 4): limit compression coexists with an incompleteness-barrier
  witness. This bundles EPIC 012’s limit pole with EPIC 003’s halting obstruction. The EPIC_001 §2.5
  **closed** summit as one `theorem` is `ic_universal_theorem_summit` in `ICUniversalTheorem.lean`
  (different conjunction). -/
theorem reflexive_architecture_limit_and_incompleteness_barrier :
    (∃ i : CompressionInstance Unit,
        i.polarity = CompressionPolarity.limit ∧ i.profile.hasRepresentationEconomy) ∧
      (∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p) :=
  And.intro reflexive_architecture_limit_corollary witness_incompleteness_barrier

end InfinityCompression.Frontier
