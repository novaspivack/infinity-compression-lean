/-
  EPIC_012_UQ1 — **Route Uniqueness** (Program V / UQ, Module 2).

  Proves full uniqueness of adequate routes up to `RouteEquiv`.

  **T-UQ.5** — `adequate_route_equiv_ci` — every adequate route is route-equivalent to the
  CI route. Forward map = route.compare (from `adequate_route_maps_to_ciRoute`). Backward map
  is the constant map to a chosen element of `route.R`.

  **T-UQ.6** — `ci_unique_up_to_route_equivalence` — CI is unique up to `RouteEquiv`.

  **T-UQ.7** — `nems_all_adequate_equiv_ci` — NEMS corollary.

  **Key lemma:** The backward map from `ciRoute` to any adequate route is the constant map
  to `adequateRoute_chosenElement route`. This is a valid route map because:
  - ciRoute.certify x = forgetToBareCanonical x = canonicalBareCertificate (by T-FC.1a)
  - route.certify (chosen) = canonicalBareCertificate (by singleton lemma)
  - Therefore ciRoute.certify x = route.certify (chosen).
-/

import InfinityCompression.MetaProof.RouteEquivalence

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## Chosen element of an adequate route carrier -/

/-- For any adequate route, choose a fixed element from its carrier.
  The carrier is nonempty because the nondegeneracy condition provides two elements. -/
noncomputable def adequateRoute_chosenElement {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) : route.R :=
  route.nondegenerate.choose

/-! ## Backward map: ciRoute → any adequate route -/

/-- The backward route map from `ciRoute` to any adequate route.

  Every element of `ciRoute.R = EnrichedReflectiveSplit BD n A` maps to
  `adequateRoute_chosenElement route`.

  This is a valid route map because both `ciRoute.certify x` and
  `route.certify (chosen)` equal `canonicalBareCertificate`:
  - `ciRoute.certify x = forgetToBareCanonical x = canonicalBareCertificate` (T-FC.1a)
  - `route.certify (chosen) = canonicalBareCertificate` (singleton lemma) -/
noncomputable def ciToRoute_backMap {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A)
    (route : AdequateReflectiveRoute BD n A) :
    RouteMap (ciRoute H hne hce) route where
  toFun := fun _ => adequateRoute_chosenElement route
  certify_comm := fun x => by
    simp only [ciRoute]
    rw [adequate_route_certify_eq_canonical route (adequateRoute_chosenElement route),
        enriched_reflective_split_forgets_to_canonical_bare_certificate x]

/-! ## T-UQ.5 — Every adequate route is route-equivalent to the CI route -/

/-- **T-UQ.5** — Every adequate route is `RouteEquiv`-equivalent to `ciRoute`.

  Forward map: `route.compare` (maps route.R → ciRoute.R = EnrichedReflectiveSplit,
  commutes with certification by soundness + singleton).
  Backward map: constant map to `adequateRoute_chosenElement route`. -/
noncomputable def adequate_route_equiv_ci {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A)
    (route : AdequateReflectiveRoute BD n A) :
    RouteEquiv route (ciRoute H hne hce) :=
  RouteEquiv.mk_of_maps
    (adequate_route_maps_to_ciRoute H hne hce route).some
    (ciToRoute_backMap H hne hce route)

/-! ## T-UQ.6 — CI is unique up to route equivalence -/

/-- **T-UQ.6** — The CI route is unique up to `RouteEquiv` among adequate routes:
  any adequate route is equivalent to `ciRoute`. -/
theorem ci_unique_up_to_route_equivalence {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A)
    (route : AdequateReflectiveRoute BD n A) :
    Nonempty (RouteEquiv route (ciRoute H hne hce)) :=
  ⟨adequate_route_equiv_ci H hne hce route⟩

/-! ## T-UQ.7 — NEMS corollary -/

/-- **T-UQ.7** — All adequate routes on the NEMS spine are route-equivalent to the NEMS CI route. -/
noncomputable def nems_all_adequate_equiv_ci
    (H : SummitComponentExtraction nemsSpineChain.toArchitecture)
    (route : AdequateReflectiveRoute _ _ nemsSpineChain.toArchitecture) :
    RouteEquiv route (nems_ciRoute_is_adequate H) :=
  adequate_route_equiv_ci H
    ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, nems_role_skeletons_ne⟩
    nems_spine_architecture_crown_eligible
    route

end InfinityCompression.MetaProof
