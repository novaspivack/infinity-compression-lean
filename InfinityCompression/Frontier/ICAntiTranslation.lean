/-
  EPIC_001 §7.5 — Anti-translation interface (IC-only universal laws).

  Checkpoint C asks that UL-3/UL-4 not be *mere relabeling* of NEMS. A **structural** answer
  available in *this* repository is: the flagship obstruction theorems are stated and proved for
  abstract `FaithfulSelfPresentation` + `GlobalRealizationSpace` + the EPIC 017 typeclass bundle,
  with `DiagonalCapable` importing the halting barrier only through Mathlib’s `ComputablePred`
  machinery (`FailureModes.witness_incompleteness_barrier`). No `nems-lean` import participates.

  This module does **not** construct a dominance theorem comparing IC axioms to a formalized NEMS
  axiom list in the same logic — that would require importing or duplicating a NEMS foundation.
  It **does** expose the polymorphic UL-3 corollary under a single name for readers and auditors.
-/

import InfinityCompression.Core.CompletionOperatorClass
import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Schemas.NegativeDiagonal
import InfinityCompression.Schemas.NonVacuity

import InfinityCompression.Frontier.InternalCompressionWithoutTotalization
import InfinityCompression.Frontier.NoFinalPositiveCompressor

universe u1 u2 u3 u4 u5

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Schemas

/-- UL-3 (nonempty form): abstract `FaithfulSelfPresentation` + `DiagonalCapable` ⇒ no
  `CompletionOperatorClass`. Same statement as `no_final_positive_compressor_nonempty`; kept here
  as the **polymorphic** entry point for anti-translation audits. -/
theorem ul3_no_final_positive_compressor_ic_abstract
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    {opposes : V → V → Prop}
    (F : FaithfulSelfPresentation I L C V)
    (GRS : GlobalRealizationSpace G C V)
    [AntiContactRule F.toSPF opposes]
    [HasRepresentability F.toSPF opposes]
    (hD : DiagonalCapable F.toSPF GRS) :
    ¬ ∃ _ : CompletionOperatorClass (FaithfulSelfPresentation I L C V) (fun F => F.toSPF) GRS, True :=
  @no_final_positive_compressor_nonempty I L C V G opposes F GRS _ _ hD

/-- UL-4 bundle: partial completion on a singleton witness + no total `CompletionOperatorClass` on
  the diagonal `allInadmissibleGRS` instance — same as `internal_compression_without_totalization`. -/
theorem ul4_internal_compression_without_totalization_ic_abstract
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    {opposes : V → V → Prop}
    (F : FaithfulSelfPresentation I L C V)
    (GRS : GlobalRealizationSpace G C V)
    [AntiContactRule F.toSPF opposes]
    [HasRepresentability F.toSPF opposes]
    (hD : DiagonalCapable F.toSPF GRS) :
    (∃ F' : FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool,
        Nonempty (CompletionWitness F'.toSPF nv27GRS)) ∧
      ¬ ∃ _ : CompletionOperatorClass (FaithfulSelfPresentation I L C V) (fun F => F.toSPF) GRS,
        True :=
  @internal_compression_without_totalization I L C V G opposes F GRS _ _ hD

end InfinityCompression.Frontier
