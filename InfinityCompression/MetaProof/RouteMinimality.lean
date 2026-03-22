/-
  EPIC_011_UR1 — **Route Minimality** (Program U, Module 4).

  Proves that every adequate route maps to the CI route (the canonical enriched route) in a
  natural route preorder. This is the correct sense of CI minimality: every adequate route
  expresses itself through the CI architecture via the comparison map.

  **D-U.7** — `RouteMap` — a certification-preserving map between two routes.

  **D-U.8** — `RouteLE` — route preorder: `route₁ ≤ route₂` iff there is a `RouteMap` from
  `route₁` to `route₂`.

  **T-U3.1** — `routeLE_refl` — the route preorder is reflexive.

  **T-U3.2** — `routeLE_trans` — the route preorder is transitive.

  **T-U3.3** — `adequate_route_maps_to_ciRoute` — **every adequate route maps to the CI route**
  (via its comparison map). The CI route is thus a **coretraction** / universal target
  in the category of adequate routes.

  **T-U3.4** — `ciRoute_minimal` — for any architecture with two distinct role skeletons,
  all adequate routes satisfy `RouteLE route ciRoute`.

  **Remark on direction:** The preorder direction `route ≤ ciRoute` says the CI route is
  an "upper bound" that every adequate route maps into. This is the correct sense in which
  the CI architecture is minimal / canonical: it is the image that absorbs all adequate routes.
-/

import InfinityCompression.MetaProof.RouteNecessity

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## D-U.7 — Route Map -/

/-- **D-U.7** — A **route map** from `route₁` to `route₂` is a function `f : route₁.R → route₂.R`
  that commutes with the certification maps. -/
structure RouteMap {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route₁ route₂ : AdequateReflectiveRoute BD n A) where
  /-- Underlying function on carrier types. -/
  toFun : route₁.R → route₂.R
  /-- The function commutes with certification. -/
  certify_comm : ∀ r : route₁.R, route₁.certify r = route₂.certify (toFun r)

/-! ## D-U.8 — Route Preorder -/

/-- **D-U.8** — Route preorder: `route₁ ≤ route₂` iff there is a `RouteMap` from `route₁` to `route₂`. -/
def RouteLE {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route₁ route₂ : AdequateReflectiveRoute BD n A) : Prop :=
  Nonempty (RouteMap route₁ route₂)

/-! ## T-U3.1 — Route preorder is reflexive -/

/-- **T-U3.1** — The route preorder is reflexive: the identity is a route map. -/
theorem routeLE_refl {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) : RouteLE route route :=
  ⟨⟨id, fun _ => rfl⟩⟩

/-! ## T-U3.2 — Route preorder is transitive -/

/-- **T-U3.2** — The route preorder is transitive: route maps compose. -/
theorem routeLE_trans {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (r₁ r₂ r₃ : AdequateReflectiveRoute BD n A)
    (h₁₂ : RouteLE r₁ r₂) (h₂₃ : RouteLE r₂ r₃) : RouteLE r₁ r₃ := by
  obtain ⟨f₁₂⟩ := h₁₂
  obtain ⟨f₂₃⟩ := h₂₃
  exact ⟨⟨f₂₃.toFun ∘ f₁₂.toFun,
    fun r => (f₁₂.certify_comm r).trans (f₂₃.certify_comm (f₁₂.toFun r))⟩⟩

/-! ## T-U3.3 — Every adequate route maps to the CI route -/

/-- **T-U3.3** — Any adequate route `route` admits a route map to the CI route.

  The witness is `route.compare : route.R → EnrichedReflectiveSplit BD n A`.
  - This is exactly a function from `route.R` to the CI route's carrier.
  - By soundness, `route.certify r = forgetToBareCanonical (route.compare r)` = `ciRoute.certify (route.compare r)`.

  Therefore, every adequate route maps into the CI architecture. -/
theorem adequate_route_maps_to_ciRoute {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A)
    (route : AdequateReflectiveRoute BD n A) :
    RouteLE route (ciRoute H hne hce) :=
  ⟨⟨route.compare, fun r => route.sound r⟩⟩

/-! ## T-U3.4 — CI minimality -/

/-- **T-U3.4 (CI Minimality)** — For any architecture with two distinct role skeletons,
  every adequate route maps to the CI route.

  This is the universal necessity of the enriched forgetful route architecture:
  no adequate route can avoid passing through the CI route. -/
theorem ciRoute_minimal {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A) :
    ∀ route : AdequateReflectiveRoute BD n A, RouteLE route (ciRoute H hne hce) :=
  fun route => adequate_route_maps_to_ciRoute H hne hce route

/-! ## T-U3.5 — NEMS corollary -/

/-- **T-U3.5** — All adequate routes on the NEMS spine map to the NEMS CI route. -/
theorem nems_all_adequate_routes_map_to_ciRoute (H : SummitComponentExtraction nemsSpineChain.toArchitecture)
    (route : AdequateReflectiveRoute _ _ nemsSpineChain.toArchitecture) :
    RouteLE route (nems_ciRoute_is_adequate H) :=
  adequate_route_maps_to_ciRoute H
    ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, nems_role_skeletons_ne⟩
    nems_spine_architecture_crown_eligible
    route

end InfinityCompression.MetaProof
