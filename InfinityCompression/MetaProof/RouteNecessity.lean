/-
  EPIC_011_UR1 — **Route Necessity** (Program U, Module 3).

  Proves the core universal necessity results:

  **T-U2.1** — `bareCollapsed_not_adequate` — A bare-collapsed route is not adequate: it cannot
  satisfy the nondegeneracy condition. This closes the "bare-only routes are insufficient" claim.

  **T-U2.2** — `adequate_route_is_enrichedForgetful` — Any adequate route is enriched-forgetful.
  The certification/realization split is structurally necessary for any adequate route.

  **T-U2.3** — `adequate_route_factors_through_enriched` — Any adequate route has a canonical map
  to the CI route (EnrichedReflectiveSplit + forgetToBareCanonical): its comparison map.
  This is the **route necessity** / factorization theorem (Program U, T-U1).

  **T-U2.4** — `nems_adequate_is_enrichedForgetful` — The NEMS spine CI route is adequate and
  enriched-forgetful (concrete witness that adequate routes exist and the result is non-vacuous).

  **scope:** Necessity proofs. Minimality and preorder are in `RouteMinimality.lean`.
-/

import InfinityCompression.MetaProof.RouteClasses

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## T-U2.1 — Bare-collapsed routes are not adequate -/

/-- **T-U2.1** — A bare-collapsed route cannot be adequate.

  **Proof:** Adequacy requires nondegeneracy (`RouteNondegeneracy compare`), which is exactly
  `ProperExtensionViaForgetful (forgetToBareCanonical ∘ compare)`.
  But a bare-collapsed route requires `Function.Injective (forgetToBareCanonical ∘ compare)`.
  These are logically contradictory if the carrier type `R` is nonempty and the bare layer has
  any two distinct preimages (which the adequacy condition itself forces). -/
theorem bareCollapsed_not_adequate {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {R : Type} (_certify : R → BareCanonicalCertificate)
    (compare : R → EnrichedReflectiveSplit BD n A)
    (hbc : BareCollapsedRoute compare)
    (hnd : RouteNondegeneracy compare) : False := by
  obtain ⟨x₁, x₂, hne, heq⟩ := hnd
  exact hne (hbc heq)

/-- **Corollary** — A route cannot simultaneously be bare-collapsed and satisfy all adequacy conditions. -/
theorem bareCollapsed_inadequate {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {R : Type} (certify : R → BareCanonicalCertificate)
    (compare : R → EnrichedReflectiveSplit BD n A)
    (hbc : BareCollapsedRoute compare) :
    ¬ (RouteSoundness certify compare ∧ RouteCanonicalLanding certify ∧ RouteNondegeneracy compare) :=
  fun ⟨_, _, hnd⟩ => bareCollapsed_not_adequate certify compare hbc hnd

/-! ## T-U2.2 — Adequate routes are enriched-forgetful -/

/-- **T-U2.2** — Any adequate route is enriched-forgetful.

  **Proof:** Adequacy includes nondegeneracy, and enriched-forgetful is identical to nondegeneracy.
  This is immediate from the definitions. -/
theorem adequate_route_is_enrichedForgetful {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) :
    EnrichedForgetfulRoute route.compare :=
  (enrichedForgetfulRoute_iff_nondegenerate route.compare).mpr route.nondegenerate

/-! ## T-U2.3 — Route Necessity / Factorization -/

/-- **T-U2.3** — Any adequate route factors through the CI enriched route:
  the comparison map `route.compare` witnesses the factorization.

  More precisely, for any adequate route `(R, certify, compare)`, the diagram:
  ```
  R ───compare──→ EnrichedReflectiveSplit BD n A
  │                            │
  certify               forgetToBareCanonical
  │                            │
  └──────────────→ BareCanonicalCertificate
  ```
  commutes (by soundness), and the CI route is the codomain of `compare`.

  This is the key universality theorem: the CI route architecture is not merely exhibited;
  it is the necessary landing space for any adequate route. -/
theorem adequate_route_factors_through_enriched {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) :
    ∃ (f : route.R → EnrichedReflectiveSplit BD n A),
      (∀ r : route.R, route.certify r = forgetToBareCanonical (f r)) ∧
      ProperExtensionViaForgetful (forgetToBareCanonical ∘ f) :=
  ⟨route.compare, route.sound, route.nondegenerate⟩

/-- **T-U2.3a** — The factorization map is the comparison map (no other choices needed). -/
theorem adequate_route_comparison_is_factorization {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) (r : route.R) :
    route.certify r = forgetToBareCanonical (route.compare r) :=
  route.sound r

/-! ## T-U2.4 — Non-vacuity: NEMS adequate CI route -/

/-- **T-U2.4** — The NEMS adequate route is enriched-forgetful (non-vacuity of the necessity theorem). -/
theorem nems_adequate_is_enrichedForgetful (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    EnrichedForgetfulRoute (nems_ciRoute_is_adequate H).compare :=
  adequate_route_is_enrichedForgetful (nems_ciRoute_is_adequate H)

/-- **Summary theorem** — Every adequate route to reflective certification is enriched-forgetful,
  and the CI route (EnrichedReflectiveSplit + forgetToBareCanonical) is the canonical witness.
  Bare-collapsed routes are structurally excluded from adequacy. -/
theorem universal_route_necessity {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) :
    EnrichedForgetfulRoute route.compare ∧
      ¬ BareCollapsedRoute route.compare ∧
      ∃ (f : route.R → EnrichedReflectiveSplit BD n A),
        (∀ r, route.certify r = forgetToBareCanonical (f r)) ∧
        ProperExtensionViaForgetful (forgetToBareCanonical ∘ f) :=
  ⟨adequate_route_is_enrichedForgetful route,
    fun hbc => bareCollapsed_not_adequate route.certify route.compare hbc route.nondegenerate,
    adequate_route_factors_through_enriched route⟩

end InfinityCompression.MetaProof
