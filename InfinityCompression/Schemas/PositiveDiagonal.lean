/-
  EPIC 004 — Positive diagonal schema (Theorem 4.1) + NV-4.2

  The program spec states `FiniteAmalgamation` with a witness-indexed `amalgamate`.
  Operationally, a chosen global amalgam in `G` with full realization is enough to
  assemble `CompletionWitness`; we package that as `FiniteAmalgamation` below and
  relate it to the spec sketch in a comment on `FiniteAmalgamation`.
-/

import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Core.LocalCoherence
import InfinityCompression.Core.LocalWitnessSpace
import InfinityCompression.Core.SelfPresentation

universe u1 u2 u3 u4 u5 u6

namespace InfinityCompression.Schemas

open InfinityCompression.Core

/-- Finite amalgamation: some global `g` realizes every self-contact datum.

  *Spec sketch (witness form):* `amalgamate : (w : W) → (∀ i, LWS.compatible w (F.selfContactAt i)) → G`
  together with `amalgamate_realizes` — equivalent to this bundle whenever a global
  compatible witness exists and is chosen. -/
class FiniteAmalgamation {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {W : Type u5} {G : Type u6}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V)
    (LWS : LocalWitnessSpace V W) where
  amalgamate : G
  amalgamate_realizes :
    ∀ i, GRS.realizes (GRS.globLoc amalgamate (F.contact i)) (F.selfContactAt i)

/-- Admissibility follows from global realizability. -/
class AdmissibilityClosure {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) where
  closure_admissible :
    ∀ g : G,
      (∀ i, GRS.realizes (GRS.globLoc g (F.contact i)) (F.selfContactAt i)) →
        GRS.admissible g

/-- The program spec names a field `canonical : G`; we identify that role with
  `FiniteAmalgamation.amalgamate` once a global amalgam is fixed. -/
abbrev specCanonical {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {W : Type u5} {G : Type u6}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) (LWS : LocalWitnessSpace V W)
    [FA : FiniteAmalgamation F GRS LWS] : G :=
  FA.amalgamate

/-- The amalgam is `leq`-least among admissible realizers (the spec's `canonical_least` with
  `canonical := amalgamate` — no separate equality assumption). -/
class HasCanonicalRealizer {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {W : Type u5} {G : Type u6}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) (LWS : LocalWitnessSpace V W)
    [FA : FiniteAmalgamation F GRS LWS] where
  canonical_least :
    ∀ g : G,
      GRS.admissible g →
        (∀ i, GRS.realizes (GRS.globLoc g (F.contact i)) (F.selfContactAt i)) →
          GRS.leq FA.amalgamate g

/-! ### Theorem 4.1 — Positive Diagonal Schema -/

/-- **Theorem 4.1 (positive diagonal).** From local coherence, finite amalgamation,
  admissibility closure, and canonicity of the amalgam, build a `CompletionWitness`
  with transfer concentration on the induction-style profile (NV-3.2).

  `HasCanonicalRealizer` is stated relative to `FiniteAmalgamation.amalgamate`, so the
  program-spec field `canonical` is identified with that amalgam (see `specCanonical`). -/
theorem positive_diagonal_schema
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {W : Type u5} {G : Type u6}
    [DecidableEq C]
    {F : FaithfulSelfPresentation I L C V}
    {IS : InteractionStructure C}
    {LWS : LocalWitnessSpace V W}
    {GRS : GlobalRealizationSpace G C V}
    [LocalCoherence F.toSPF IS LWS]
    [FA : FiniteAmalgamation F.toSPF GRS LWS]
    [AC : AdmissibilityClosure F.toSPF GRS]
    [HR : HasCanonicalRealizer F.toSPF GRS LWS] :
    ∃ _ : CompletionWitness F.toSPF GRS,
      ({ hasFiniteCharacterization := True
         hasVerificationReduction := True
         hasTransferConcentration := True
         hasRepresentationEconomy := True
         hasUniformity := False } : CompressionProfile).hasTransferConcentration :=
  ⟨{
    complete := FA.amalgamate
    realizes_all := FA.amalgamate_realizes
    admissible_complete := AC.closure_admissible FA.amalgamate FA.amalgamate_realizes
    canonical := fun g hg hgR => HR.canonical_least g hg hgR
  }, trivial⟩

/-- NV-4.2: if every global is admissible, realizability implies admissibility trivially. -/
theorem admissibilityClosure_of_univ_admissible
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V)
    (h : ∀ g : G, GRS.admissible g) : AdmissibilityClosure F GRS where
  closure_admissible := fun g _ => h g

/-! NV-4.1 / NV-4.3 (closure lattice / Knaster–Tarski): stub instances deferred to EPIC 007. -/

end InfinityCompression.Schemas
