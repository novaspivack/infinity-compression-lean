/-
  EPIC 015 — Frontier: positive decomposition (UL-2 anatomy).

  `HasFiniteTracking` and `HasGluing` are formalized at the IC layer via `CompressionProfile`
  fields (Def 3.2). This is the **surrogate** for APS paper predicates until an APS import
  refines the mapping; T-15.1 is then purely definitional bookkeeping.

  The **full** C-15.1 claim (“every positive instance decomposes”) is **not** proved here:
  positive `CompressionInstance`s can satisfy nontriviality via TC or VR alone without both
  facets. We prove decomposition for an explicit **suitable** subclass (`SuitablePositiveCompression`).
-/

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionInstance

universe u

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Meta

/-- IC surrogate for APS “finite tracking”: finite characterization in the compression profile. -/
def HasFiniteTracking {BD : Type u} (ci : CompressionInstance BD) : Prop :=
  ci.profile.hasFiniteCharacterization

/-- IC surrogate for APS “gluing”: representation economy in the compression profile. -/
def HasGluing {BD : Type u} (ci : CompressionInstance BD) : Prop :=
  ci.profile.hasRepresentationEconomy

/-- Paper-level `IcompIdx`: both anatomy facets at the profile layer (per EPIC 015 manifest). -/
def IcompIdx {BD : Type u} (ci : CompressionInstance BD) : Prop :=
  HasFiniteTracking ci ∧ HasGluing ci

/-- T-15.1 — bookkeeping: `IcompIdx` is exactly finite-tracking ∧ gluing at this layer. -/
theorem aps_composition_is_positive_ic {BD : Type u} (ci : CompressionInstance BD) :
    IcompIdx ci ↔ HasFiniteTracking ci ∧ HasGluing ci :=
  Iff.rfl

/-- Explicit **suitable** class: positive polarity plus both profile facets present.

  This is the natural IC class for which C-15.1-style decomposition is **immediate** from
  definitions (strong partial result toward Level 2 / EPIC 015). -/
def SuitablePositiveCompression {BD : Type u} (ci : CompressionInstance BD) : Prop :=
  ci.polarity = CompressionPolarity.positive ∧
    ci.profile.hasFiniteCharacterization ∧ ci.profile.hasRepresentationEconomy

/-- Crown-aligned positive class: suitable **and** profile pinned to the induction spine profile
  (`nv32InductionProfile`). Use this when the positive pillar must match the NEMS spine / reflexive
  layer rather than an arbitrary suitable instance. -/
def CrownPositiveCompression {BD : Type u} (ci : CompressionInstance BD) : Prop :=
  SuitablePositiveCompression ci ∧ ci.profile = nv32InductionProfile

/-- Strong partial (EPIC 015 risk register): suitable positive instances carry `IcompIdx`. -/
theorem suitable_positive_implies_ic_anatomy {BD : Type u} (ci : CompressionInstance BD)
    (h : SuitablePositiveCompression ci) : IcompIdx ci :=
  ⟨h.2.1, h.2.2⟩

theorem crown_positive_implies_ic_anatomy {BD : Type u} (ci : CompressionInstance BD)
    (h : CrownPositiveCompression ci) : IcompIdx ci :=
  suitable_positive_implies_ic_anatomy ci h.1

/-- Sharp characterization: “suitable positive” is exactly **positive polarity** plus `IcompIdx`
  at this layer (equivalently: both profile facets). This is the strongest **definitional** closure
  for EPIC 015 before an APS-imported predicate refines the surrogates. -/
theorem suitable_positive_iff_positive_and_ic_anatomy {BD : Type u} (ci : CompressionInstance BD) :
    SuitablePositiveCompression ci ↔
      ci.polarity = CompressionPolarity.positive ∧ IcompIdx ci := by
  constructor
  · intro h
    exact ⟨h.1, suitable_positive_implies_ic_anatomy ci h⟩
  · rintro ⟨hp, hidx⟩
    rcases hidx with ⟨hfc, hgl⟩
    exact ⟨hp, hfc, hgl⟩

/-- Naive C-15.1 (“every positive instance has `IcompIdx`”) — **false** at this layer: nontriviality
  only requires `TC ∨ VR`, so a positive instance can carry transfer concentration without both
  `hasFiniteCharacterization` and `hasRepresentationEconomy`. The right EPIC 015 target is a
  **suitable** subclass (`SuitablePositiveCompression`) or an APS-sharp predicate, not this ∀.

  Quantified over `Type` (Lean’s `Type 0`) so counterexamples like `Unit` instantiate without
  universe mismatch. -/
def positive_compression_decomposition_conjecture : Prop :=
  ∀ (BD : Type) (ci : CompressionInstance BD),
    ci.polarity = CompressionPolarity.positive → IcompIdx ci

private def ci_positive_transfer_only : CompressionInstance Unit :=
  { polarity := CompressionPolarity.positive
    source := ()
    target := ()
    profile := compressionProfileOfIndex ⟨4, by decide⟩
    nontrivial := Or.inl (by
      -- profile `4` has `hasTransferConcentration` only (`0b00100`).
      simp [compressionProfileOfIndex]; native_decide) }

private lemma not_icompIdx_ci_positive_transfer_only : ¬ IcompIdx ci_positive_transfer_only := by
  rintro ⟨hfc, _⟩
  -- `HasFiniteTracking` is `hasFiniteCharacterization` on profile `4` (= `False` as `Prop`).
  simp [ci_positive_transfer_only, HasFiniteTracking, compressionProfileOfIndex] at hfc

/-- The naive universal `positive_compression_decomposition_conjecture` is refuted (SEP-3.3 profile `i = 4`). -/
theorem positive_compression_decomposition_conjecture_false :
    ¬ positive_compression_decomposition_conjecture := by
  intro h
  exact not_icompIdx_ci_positive_transfer_only (h Unit ci_positive_transfer_only rfl)

end InfinityCompression.Frontier
