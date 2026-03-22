/-
  EPIC_001 §2.5 — IC Universal Theorem (summit) as one closed proposition.

  The prose target speaks of liftability anatomy, obstruction/remainder, and
  non-totalizability of control machinery. Here those themes are unpacked into
  **proved** IC statements already in the library (UL-2 partial, UL-1-style witness,
  UL-3/UL-4 via one diagonal bundle). This is the formal summit **as far as the
  current development discharges it**; it does not add new mathematical content
  beyond combining existing theorems.

  **`ic_universal_theorem_landscape`** (below) is the strongest single packaged conjunction in this
  file: §2.5 summit + UL-5 selectivity + Level-4 reflexive/incompleteness bundle + honest EPIC 015
  refutation of naive C-15.1 — still no new proof obligations, only aggregation.
-/

import Mathlib.Computability.Halting

import InfinityCompression.Core.CompletionOperatorClass
import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.FailureModes
import InfinityCompression.Schemas.NonVacuity

import InfinityCompression.Frontier.CompressionSelectivity
import InfinityCompression.Frontier.InternalCompressionWithoutTotalization
import InfinityCompression.Frontier.NoFinalPositiveCompressor
import InfinityCompression.Frontier.PositiveDecomposition
import InfinityCompression.Frontier.ReflexiveArchitecture

universe u

namespace InfinityCompression.Frontier

open ComputablePred Nat.Partrec.Code
open InfinityCompression.Core
open InfinityCompression.Meta
open InfinityCompression.Schemas

/-- Concrete positive instance with both profile facets (NV-32 induction profile). -/
private def summitSuitablePositive : CompressionInstance Unit :=
  { polarity := CompressionPolarity.positive
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

private lemma summitSuitable : SuitablePositiveCompression summitSuitablePositive := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [summitSuitablePositive, nv32InductionProfile]
  · simp [summitSuitablePositive, nv32InductionProfile]

private lemma summitIcompIdx : IcompIdx summitSuitablePositive :=
  suitable_positive_implies_ic_anatomy summitSuitablePositive summitSuitable

/-- UL-2 fragment + UL-1-style amalgamation obstruction (first conjunct of §2.5 summit). -/
def icUniversalSummitStatementAnatomyAmalg : Prop :=
  (∃ ci : CompressionInstance Unit, SuitablePositiveCompression ci ∧ IcompIdx ci) ∧
    ¬ Nonempty (CompletionWitness amalgWitnessFaithful.toSPF standardBoolGRS3)

/-- UL-3/UL-4 diagonal bundle (second conjunct of §2.5 summit). -/
def icUniversalSummitStatementInternalUl34 : Prop :=
  (∃ F' : FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool,
      Nonempty (CompletionWitness F'.toSPF nv27GRS)) ∧
    ¬∃ _ : CompletionOperatorClass (FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool)
        (fun F => F.toSPF) allInadmissibleGRS, True

/-- Proposition of `ic_universal_theorem_summit` (needed so later theorems can conjoin it without the
  theorem name being parsed as a proof term in the statement). -/
def icUniversalSummitStatement : Prop :=
  icUniversalSummitStatementAnatomyAmalg ∧ icUniversalSummitStatementInternalUl34

/-- UL-5 compression selectivity (landscape conjunct). -/
def ul5SelectivityStatement : Prop :=
  ∃ (F : FaithfulSelfPresentation (Fin 3) (Fin 3) (Fin 3) Bool)
    (GRS : GlobalRealizationSpace Bool (Fin 3) Bool)
    (opposes : Bool → Bool → Prop),
    ¬ Nonempty (CompletionWitness F.toSPF GRS) ∧
      ¬ Nonempty (EscapeWitness (W := Unit) F.toSPF opposes)

/-- Level-4 reflexive limit + incompleteness-barrier fragment (landscape conjunct). -/
def reflexiveLevel4CompanionStatement : Prop :=
  (∃ i : CompressionInstance Unit,
      i.polarity = CompressionPolarity.limit ∧ i.profile.hasRepresentationEconomy) ∧
    (∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p)

/-- Naive C-15.1 universal refuted (landscape conjunct). -/
def naiveC15RefutedStatement : Prop :=
  ¬ positive_compression_decomposition_conjecture

/-- Full landscape proposition (§2.5 summit + UL-5 + Level-4 companion + naive C-15 refutation). -/
def icUniversalLandscapeStatement : Prop :=
  icUniversalSummitStatement ∧
    ul5SelectivityStatement ∧
    reflexiveLevel4CompanionStatement ∧
    naiveC15RefutedStatement

/-- UL-2 fragment plus UL-1-style amalgamation obstruction (first two conjuncts of the §2.5 summit). -/
lemma ic_summit_anatomy_and_amalgamation_obstruction :
    icUniversalSummitStatementAnatomyAmalg := by
  refine ⟨?_, ?_⟩
  · refine ⟨summitSuitablePositive, ?_, ?_⟩
    · exact summitSuitable
    · exact summitIcompIdx
  · exact no_completion_amalgWitness

/-- UL-3/UL-4 diagonal bundle: same proposition as `internal_compression_without_totalization` on NV-28. -/
theorem ic_summit_internal_compression_ul34 :
    icUniversalSummitStatementInternalUl34 := by
  -- Proof is the original theorem; `@` pins universes and `opposes` so TC search succeeds.
  exact
    @internal_compression_without_totalization (Fin 1) (Fin 1) (Fin 1) Bool Bool (· ≠ ·) nv28Family allInadmissibleGRS _ _
      diagonalCapable_nv28_allInadmissible

/-- **Theorem (summit).** EPIC_001 §2.5 IC Universal Theorem — one closed conjunction: anatomy and amalg
  obstruction, plus internal compression without totalization (UL-3/UL-4 bundle). -/
theorem ic_universal_theorem_summit : icUniversalSummitStatement :=
  ⟨ic_summit_anatomy_and_amalgamation_obstruction, ic_summit_internal_compression_ul34⟩

/-- **Maximal landscape (same proof layer).** Aggregates the §2.5 summit, UL-5 compression selectivity,
  the Level-4 reflexive limit + incompleteness-barrier bundle, and the refutation of naive C-15.1.

  This is the largest **single** `theorem` statement obtained by conjoining already-proved frontier
  results without new lemmas. It does not add mathematical content beyond packaging; use it when the
  narrative goal is “whole program in one shot,” not the minimal §2.5 summit alone. -/
theorem ic_universal_theorem_landscape : icUniversalLandscapeStatement :=
  ⟨ic_universal_theorem_summit,
    ⟨compression_selectivity,
      ⟨reflexive_architecture_limit_and_incompleteness_barrier,
        positive_compression_decomposition_conjecture_false⟩⟩⟩

/-- **Summit layer S3 (dependency surrogate).** The §2.5 summit is **biconditional** with the two
  proved lemma families (anatomy/amalg + internal UL-3/4). Any proof of the summit must pass through
  both poles; there is no single-shot axiom shortcut in this library.

  In a `theorem` statement, a lemma identifier denotes its **proof term**, not the proposition; the
  named `def`s `icUniversalSummitStatementAnatomyAmalg` / `icUniversalSummitStatementInternalUl34`
  avoid that ambiguity. -/
theorem ic_universal_theorem_summit_iff_components :
    icUniversalSummitStatement ↔
      (icUniversalSummitStatementAnatomyAmalg ∧ icUniversalSummitStatementInternalUl34) :=
  Iff.intro (fun h => ⟨h.1, h.2⟩) (fun ⟨ha, hb⟩ => ⟨ha, hb⟩)

end InfinityCompression.Frontier
