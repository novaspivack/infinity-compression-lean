/-
  EPIC_013_BS1 — **Reflective Certification Architecture** (Program V / BS, Module 1).

  Defines the broad, IC-name-free abstract class of reflective certification architectures
  and proves that the canonical IC route instantiates it.

  **D-BS.1** — `ReflectiveCertificationArchitecture` (RCA) — a bundle of a certification type
  (`Cert`), a realization type (`Real`), a forgetful map `π : Real → Cert`, a proof that `Cert`
  is a singleton (canonical collapse), and a proof that `π` is a proper extension (realization
  multiplicity).

  **D-BS.2** — `RCAMorphism` — a certification-commuting map between two RCAs.

  **T-BS.1** — `ciRCA` — the CI route architecture is an RCA instance.

  **T-BS.2** — `layeredCertificationRCA` — the abstract layered certification pattern
  (any nontrivial-carrier system with a unique canonical certificate) is an RCA instance.
  This is the key non-NEMS/CI abstract instance proving the class is non-parochial.

  **scope:** Abstract RCA definition + IC instance + generic instance. Architecture instances
  and bridging to Program U are in `ArchitectureInstances.lean` and `BroadClassTheorems.lean`.
-/

import InfinityCompression.MetaProof.RouteEquivalence

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## D-BS.1 — Reflective Certification Architecture -/

/-- **D-BS.1** — A **reflective certification architecture** (RCA) specifies:
  - A bare certification type `Cert` that collapses to a unique canonical point,
  - A realization type `Real` with a forgetful map to `Cert`,
  - A proof that `Cert` is a singleton (canonical collapse),
  - A proof that `Real → Cert` is not injective (realization multiplicity).

  This class is stated entirely without IC-specific vocabulary. It captures the abstract
  pattern: one canonical certified answer, multiple genuinely distinct routes to it. -/
structure ReflectiveCertificationArchitecture : Type 1 where
  /-- Bare certificate type (what it means to certify a result). -/
  Cert : Type
  /-- Realization type (what it means to realize a certificate). -/
  Real : Type
  /-- Forgetful projection from realizations to certificates. -/
  forget : Real → Cert
  /-- The certification type collapses to a unique canonical point: certification is
  proof-irrelevant (the certificate does not vary across routes). -/
  cert_canonical : ∀ c₁ c₂ : Cert, c₁ = c₂
  /-- The forgetful map is a proper extension: realizations are not merely certificates
  in disguise — there exist genuinely distinct realizations over the same certificate. -/
  forget_proper : ProperExtensionViaForgetful forget

/-! ## D-BS.2 — RCA Morphism -/

/-- **D-BS.2** — A **morphism** between two reflective certification architectures is a pair of
  type maps `certMap : A₁.Cert → A₂.Cert` and `realMap : A₁.Real → A₂.Real` that commute
  with the forgetful projections. -/
structure RCAMorphism (A₁ A₂ : ReflectiveCertificationArchitecture) where
  /-- Map on certificate types. -/
  certMap : A₁.Cert → A₂.Cert
  /-- Map on realization types. -/
  realMap : A₁.Real → A₂.Real
  /-- The maps commute with forgetting. -/
  comm : ∀ r : A₁.Real, certMap (A₁.forget r) = A₂.forget (realMap r)

/-! ## T-BS.1 — The CI route architecture is an RCA -/

/-- **T-BS.1** — The canonical IC route is an instance of `ReflectiveCertificationArchitecture`.

  - `Cert` = `BareCanonicalCertificate` (which is a singleton by `bareCanonicalCertificate_unique`)
  - `Real` = `EnrichedReflectiveSplit BD n A` (for any architecture with distinct role skeletons)
  - `forget` = `forgetToBareCanonical`
  - `cert_canonical`: every bare certificate equals `canonicalBareCertificate` (singleton lemma)
  - `forget_proper`: from the strict-refinement theorem on the NEMS spine -/
def ciRCA (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ReflectiveCertificationArchitecture where
  Cert := BareCanonicalCertificate
  Real := EnrichedReflectiveSplit _ _ nemsSpineChain.toArchitecture
  forget := forgetToBareCanonical
  cert_canonical := fun c₁ c₂ => by
    rw [bareCanonicalCertificate_unique c₁, bareCanonicalCertificate_unique c₂]
  forget_proper := nems_reflective_route_strictly_refines_bare H

/-! ## T-BS.2 — Generic layered certification is an RCA -/

/-- **T-BS.2** — The **generic layered certification architecture** is an RCA instance.

  Given any type `T` with at least two distinct elements, the system where:
  - The certificate is trivial (a singleton `Unit`),
  - The realization is the type `T` (any element serves as a "tag" / route),
  - The forgetful map is the constant function,

  forms a reflective certification architecture.

  This is the key non-IC/NEMS abstract instance. It shows that the RCA class includes
  any system with a unique canonical answer and multiple valid routes, regardless of
  the specific mathematical content:

  - proof-relevant type theory (type = certificate, term = realization),
  - multi-witness verification (consensus = certificate, agent reasoning = realization),
  - canonical normal forms with multiple reduction paths (NF = certificate, path = realization),
  - any canonical-output / diverse-route epistemic system. -/
def layeredCertificationRCA (T : Type) (ht : ∃ t₁ t₂ : T, t₁ ≠ t₂) :
    ReflectiveCertificationArchitecture where
  Cert := Unit
  Real := T
  forget := fun _ => ()
  cert_canonical := fun _ _ => rfl
  forget_proper := by
    obtain ⟨t₁, t₂, hne⟩ := ht
    exact ⟨t₁, t₂, hne, rfl⟩

/-- **Corollary** — The generic layered certification architecture with any two-element type
  is an RCA. In particular, taking `T = Bool`, `T = Fin 2`, or any type with at least two
  distinct elements works. -/
example : ReflectiveCertificationArchitecture :=
  layeredCertificationRCA Bool ⟨false, true, Bool.false_ne_true⟩

/-! ## T-BS.3 — RCA composition and morphisms -/

/-- **T-BS.3** — The identity is an RCA morphism. -/
def RCAMorphism.id (A : ReflectiveCertificationArchitecture) : RCAMorphism A A where
  certMap := fun c => c
  realMap := fun r => r
  comm := fun _ => rfl

/-- **T-BS.4** — RCA morphisms compose. -/
def RCAMorphism.comp {A₁ A₂ A₃ : ReflectiveCertificationArchitecture}
    (f : RCAMorphism A₁ A₂) (g : RCAMorphism A₂ A₃) : RCAMorphism A₁ A₃ where
  certMap := g.certMap ∘ f.certMap
  realMap := g.realMap ∘ f.realMap
  comm := fun r => by
    simp only [Function.comp_apply]
    rw [f.comm, g.comm]

/-- **T-BS.5** — There is an RCA morphism from the generic layered architecture (indexed by
  `EnrichedReflectiveSplit`) to the CI architecture. -/
noncomputable def layeredToCI (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    RCAMorphism
      (layeredCertificationRCA (EnrichedReflectiveSplit _ _ nemsSpineChain.toArchitecture)
        (by obtain ⟨x₁, x₂, hne, _⟩ := nems_reflective_route_strictly_refines_bare H
            exact ⟨x₁, x₂, hne⟩))
      (ciRCA H) where
  certMap := fun _ => canonicalBareCertificate
  realMap := id
  comm := fun _ => by simp [ciRCA, enriched_reflective_split_forgets_to_canonical_bare_certificate]

end InfinityCompression.MetaProof
