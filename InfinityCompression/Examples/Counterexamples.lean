/-
  EPIC 008–009 — Counterexamples / separation (T-8.3, T-9.x references).

  EPIC 008: semantic barriers from `FailureModes` (not `EscapeWitness` certificates).
  EPIC 009: see `InfinityCompression.Schemas.NonVacuity` for T-9.1–T-9.6.
-/

import InfinityCompression.Core.FailureModes

namespace InfinityCompression.Examples

open InfinityCompression.Core

/-- Halting-style incompleteness: some predicates are not computable. -/
theorem witness_semantic_incompleteness_barrier :
    ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  witness_incompleteness_barrier

/-- SEP-3.2: `noTransfer` vs `incompletenessBarrier` (conjunction of both isolation witnesses). -/
def sep_transfer_vs_incompleteness :=
  sep_failure_5_6

/-- SEP-3.2: `noFaithfulSelfPresentation` vs `noLocalCoherence`. -/
def sep_no_spf_vs_no_local_coherence :=
  sep_failure_0_1

end InfinityCompression.Examples
