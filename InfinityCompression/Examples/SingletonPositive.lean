/-
  EPIC 007 — Canonical positive example: `Fin 1` / `Bool` singleton (NV-4.4 style).

  Wires `nv25Family` + `nv27GRS` through `FiniteAmalgamation`, `AdmissibilityClosure`,
  and `HasCanonicalRealizer`, then applies `positive_diagonal_schema`.
-/

import Mathlib.Tactic.FinCases

import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Core.LocalCoherence
import InfinityCompression.Core.LocalWitnessSpace
import InfinityCompression.Core.SelfPresentation
import InfinityCompression.Schemas.PositiveDiagonal

namespace InfinityCompression.Examples

open InfinityCompression.Core
open InfinityCompression.Schemas

/-- Same `CompletionWitness` pattern as `nv27Completion`, stated for `nv25Family.toSPF`. -/
def nv25Completion : CompletionWitness nv25Family.toSPF nv27GRS where
  complete := true
  realizes_all := fun i => by
    fin_cases i
    simp [SelfPresentedFamily.selfContactAt, nv25Family, nv27GRS]
  admissible_complete := trivial
  canonical := fun g _ hreal => by
    have hg0 := hreal ⟨0, by decide⟩
    fin_cases g <;> simp [nv27GRS, SelfPresentedFamily.selfContactAt, nv25Family] at hg0 ⊢

instance singletonFA : FiniteAmalgamation nv25Family.toSPF nv27GRS nv23WitnessSpace where
  amalgamate := true
  amalgamate_realizes := fun i => by
    fin_cases i
    simp [SelfPresentedFamily.selfContactAt, nv25Family, nv27GRS]

instance singletonAC : AdmissibilityClosure nv25Family.toSPF nv27GRS where
  closure_admissible := fun _ _ => trivial

instance singletonHR : HasCanonicalRealizer nv25Family.toSPF nv27GRS nv23WitnessSpace where
  canonical_least := fun g _ hreal => by
    have hg0 := hreal ⟨0, by decide⟩
    fin_cases g <;> simp [nv27GRS, SelfPresentedFamily.selfContactAt, nv25Family] at hg0 ⊢

/-- NV-4.4 / T-7.x: the positive diagonal schema at the singleton family. -/
theorem singleton_positive_diagonal :
    ∃ _ : CompletionWitness nv25Family.toSPF nv27GRS,
      nv32InductionProfile.hasTransferConcentration :=
  positive_diagonal_schema (F := nv25Family) (IS := nv25Interaction) (LWS := nv23WitnessSpace)
    (GRS := nv27GRS)

/-- Concrete witness (the amalgam / completion is `true`). -/
theorem singleton_positive_diagonal' :
    ∃ _ : CompletionWitness nv25Family.toSPF nv27GRS,
      nv32InductionProfile.hasTransferConcentration :=
  ⟨nv25Completion, trivial⟩

end InfinityCompression.Examples
