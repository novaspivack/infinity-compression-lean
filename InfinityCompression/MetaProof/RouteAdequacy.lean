/-
  EPIC_011_UR1 — **Route Adequacy** (Program U, Module 1).

  Defines `AdequateReflectiveRoute` — the minimal structural conditions an arbitrary reflective
  certification route must satisfy for it to be considered a genuine route to the canonical
  certification result.

  **D-U.2** — `RouteSoundness`, `RouteCanonicalLanding`, `RouteNondegeneracy` — three adequacy predicates
  (stated separately so they can be cited in subsequent modules).

  **D-U.1** — `AdequateReflectiveRoute` — a structure bundling a carrier `R` together with
  certification and comparison maps and proofs of all three conditions.

  **T-U0.1** — `adequateRoute_has_proper_extension` — any adequate route has a proper extension.

  **T-U0.2** — `ciRoute` / `nems_ciRoute_is_adequate` — the canonical IC route is adequate (non-vacuity).
-/

import InfinityCompression.MetaProof.ReflectiveRouteComparison
import InfinityCompression.MetaProof.ReflectiveFiberClassification

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## D-U.2 — Adequacy predicates -/

/-- **Soundness** predicate: certify = forgetToBareCanonical ∘ compare. -/
def RouteSoundness {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n} {R : Type}
    (certify : R → BareCanonicalCertificate)
    (compare : R → EnrichedReflectiveSplit BD n A) : Prop :=
  ∀ r : R, certify r = forgetToBareCanonical (compare r)

/-- **Canonical landing** predicate: certify always lands in the canonical bare class. -/
def RouteCanonicalLanding {R : Type}
    (certify : R → BareCanonicalCertificate) : Prop :=
  ∀ r : R, IsCanonicalBareSummitCertification (certify r).val

/-- **Nondegeneracy** predicate: forgetToBareCanonical ∘ compare is a proper extension. -/
def RouteNondegeneracy {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n} {R : Type}
    (compare : R → EnrichedReflectiveSplit BD n A) : Prop :=
  ProperExtensionViaForgetful (forgetToBareCanonical ∘ compare)

/-! ## D-U.1 — Adequate Reflective Route -/

/-- **D-U.1** — An **adequate reflective certification route** over architecture `A` bundles a
  carrier type `R : Type`, certification and comparison maps, and proofs of soundness, canonical
  landing, and nondegeneracy.

  The carrier lives in `Type` (= `Type 0`) since `EnrichedReflectiveSplit BD n A` lives in `Type`. -/
structure AdequateReflectiveRoute (BD : Type u) (n : Nat) (A : CompressionArchitecture BD n) :
    Type (u + 1) where
  /-- Carrier type. -/
  R : Type
  /-- Certification map. -/
  certify : R → BareCanonicalCertificate
  /-- Comparison map into enriched splits. -/
  compare : R → EnrichedReflectiveSplit BD n A
  /-- Soundness: certify r = forgetToBareCanonical (compare r). -/
  sound : ∀ r : R, certify r = forgetToBareCanonical (compare r)
  /-- Canonical landing. -/
  lands : ∀ r : R, IsCanonicalBareSummitCertification (certify r).val
  /-- Nondegeneracy: forgetToBareCanonical ∘ compare is a proper extension. -/
  nondegenerate : ProperExtensionViaForgetful (forgetToBareCanonical ∘ compare)

theorem adequateRoute_sound {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) : RouteSoundness route.certify route.compare :=
  route.sound

theorem adequateRoute_nondegenerate {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) : RouteNondegeneracy route.compare :=
  route.nondegenerate

/-! ## T-U0.1 — Adequate routes have proper extensions -/

/-- **T-U0.1** — Any adequate route has a non-injective comparison map. -/
theorem adequateRoute_has_proper_extension {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) :
    ProperExtensionViaForgetful (forgetToBareCanonical ∘ route.compare) :=
  route.nondegenerate

/-! ## T-U0.2 — The canonical CI route is adequate -/

/-- The **canonical IC route**: carrier = `EnrichedReflectiveSplit BD n A`, certify = forgetToBareCanonical,
  compare = id. Nondegeneracy uses two distinct role skeletons. -/
def ciRoute {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (_hce : CrownEligible A) :
    AdequateReflectiveRoute BD n A where
  R := EnrichedReflectiveSplit BD n A
  certify := forgetToBareCanonical
  compare := id
  sound := fun _ => rfl
  lands := fun x => (forgetToBareCanonical x).property
  nondegenerate := by
    obtain ⟨r₁, r₂, hne⟩ := hne
    have hs₁ := reflective_split_from_roles_standard r₁ H
    have hs₂ := reflective_split_from_roles_standard r₂ H
    have hne_m := reflective_mirror_from_roles_ne_of_roles_ne r₁ r₂ H hne
    let m₁ : ReflectiveMirrorWitness A :=
      ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₁ H
    let m₂ : ReflectiveMirrorWitness A :=
      ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₂ H
    let x₁ : EnrichedReflectiveSplit BD n A := ⟨m₁, hs₁⟩
    let x₂ : EnrichedReflectiveSplit BD n A := ⟨m₂, hs₂⟩
    refine ⟨x₁, x₂, enriched_reflective_split_ne_of_witness_ne x₁ x₂ hne_m,
      forgetToBareCanonical_eq_of_bridge_derivation_eq x₁ x₂ ?_⟩
    exact (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard r₁ H).trans
      (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard r₂ H).symm

/-- **T-U0.2** — The NEMS spine CI route is adequate. -/
def nems_ciRoute_is_adequate (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    AdequateReflectiveRoute _ _ nemsSpineChain.toArchitecture :=
  ciRoute H ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, nems_role_skeletons_ne⟩
    nems_spine_architecture_crown_eligible

end InfinityCompression.MetaProof
