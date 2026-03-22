/-
  EPIC 017 — UL-4: internal compression without totalization (T-17.2).

  The two conjuncts quantify over **different** presentations:

  * **Partial completion (first conjunct):** some `F' : FaithfulSelfPresentation (Fin 1)⁴ Bool`
    admits a `CompletionWitness` on the standard singleton `nv27GRS` (EPIC 007 closure).
    This is **not** the same `I, L, C, V` as the diagonal family `F` in the theorem parameters;
    it only shows that completion is nonempty somewhere in the landscape.

  * **No totalization (second conjunct):** for the **same** ambient `F` and `GRS` as in
    `DiagonalCapable F.toSPF GRS`, there is no `CompletionOperatorClass` on
    `FaithfulSelfPresentation I L C V` (via `no_final_positive_compressor_nonempty`).
    That tension is intentional: global partial completion exists on a small witness, while
    under full inadmissibility on `GRS` there is no total internal completion class.
-/

import InfinityCompression.Core.CompletionOperatorClass
import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Schemas.NegativeDiagonal
import InfinityCompression.Frontier.NoFinalPositiveCompressor

universe u1 u2 u3 u4 u5

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Schemas

/-- T-17.2 — partial completion exists on a singleton witness; under `DiagonalCapable`, no total class.

  First conjunct: existential over `F'` on `(Fin 1)⁴ Bool` with `nv27GRS` — not the same type
  parameters as `F`. Second conjunct: for this theorem’s `F` and `GRS`, no nonempty
  `CompletionOperatorClass` (same bundle as UL-3 / T-17.1). -/
theorem internal_compression_without_totalization
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    {opposes : V → V → Prop}
    (F : FaithfulSelfPresentation I L C V)
    (GRS : GlobalRealizationSpace G C V)
    [AntiContactRule F.toSPF opposes]
    [HasRepresentability F.toSPF opposes]
    (hD : DiagonalCapable F.toSPF GRS) :
    (∃ F' : FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool,
        Nonempty (CompletionWitness F'.toSPF nv27GRS)) ∧
      ¬ ∃ _ : CompletionOperatorClass (FaithfulSelfPresentation I L C V)
            (fun F => F.toSPF) GRS, True :=
  And.intro
    ⟨nv28Family, Nonempty.intro nv27Completion⟩
    (@no_final_positive_compressor_nonempty _ _ _ _ _ opposes F GRS _ _ hD)

end InfinityCompression.Frontier
