/-
  EPIC_012_UQ1 — **Route Equivalence** (Program V / UQ, Module 1).

  Defines the natural notions of equivalence between adequate routes and proves the key
  singleton lemma that drives all uniqueness results.

  **T-UQ.singleton** — `bareCanonicalCertificate_unique` — every `BareCanonicalCertificate`
  equals `canonicalBareCertificate`. This is the collapse of the certification layer to a point.

  **D-UQ.1** — `RouteExtensionallyEquiv` — two adequate routes are extensionally equivalent if
  their certify-maps agree (trivially, since both land on the unique `canonicalBareCertificate`)
  and their forget-images agree (also trivially, since all enriched splits forget to the same
  canonical bare certificate).

  **T-UQ.1** — `routeExtensionallyEquiv_refl/symm/trans` — extensional equivalence is an
  equivalence relation.

  **T-UQ.2** — `adequate_route_certify_eq_canonical` — any adequate route's certify-map
  always returns `canonicalBareCertificate`.

  **T-UQ.3** — `adequate_route_compare_forgets_to_canonical` — any adequate route's compare-map
  always forgets to `canonicalBareCertificate`.

  **T-UQ.4** — `adequate_routes_extensionally_equivalent` — any two adequate routes are
  extensionally equivalent to each other.

  **D-UQ.struct** — `RouteEquiv` — strong equivalence: mutual route maps that are inverse up
  to certification. Defined here; proved inhabitable in `RouteUniqueness.lean`.

  **scope:** Singleton collapse + extensional equivalence. Full structural equivalence
  is in `RouteUniqueness.lean`.
-/

import InfinityCompression.MetaProof.RouteMinimality

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## T-UQ.singleton — BareCanonicalCertificate is a singleton -/

/-- **T-UQ.singleton** — Every bare canonical certificate equals the unique canonical certificate.

  This is the key collapse: the bare certification layer has exactly one element. Every adequate
  route, regardless of its carrier or comparison map, lands on the same single point when it
  certifies. This is the "singleton lemma" that drives all uniqueness results. -/
theorem bareCanonicalCertificate_unique (c : BareCanonicalCertificate) :
    c = canonicalBareCertificate := by
  apply Subtype.ext
  exact c.property

/-! ## D-UQ.1 — Extensional route equivalence -/

/-- **D-UQ.1** — Two adequate routes over the same architecture `A` are **extensionally equivalent**
  if for every element of one route's carrier, there exists an element of the other route's carrier
  with the same certification and the same forgetful comparison image.

  Since both certify-maps return `canonicalBareCertificate` (by the singleton lemma) and both
  compare-maps forget to `canonicalBareCertificate` (by T-FC.1a), every pair of adequate routes
  is extensionally equivalent. -/
def RouteExtensionallyEquiv {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route₁ route₂ : AdequateReflectiveRoute BD n A) : Prop :=
  (∀ r₁ : route₁.R, ∃ r₂ : route₂.R,
      route₁.certify r₁ = route₂.certify r₂ ∧
      forgetToBareCanonical (route₁.compare r₁) = forgetToBareCanonical (route₂.compare r₂)) ∧
  (∀ r₂ : route₂.R, ∃ r₁ : route₁.R,
      route₂.certify r₂ = route₁.certify r₁ ∧
      forgetToBareCanonical (route₂.compare r₂) = forgetToBareCanonical (route₁.compare r₁))

/-! ## T-UQ.2 — Adequate routes always certify canonically -/

/-- **T-UQ.2** — The certify-map of any adequate route always returns `canonicalBareCertificate`.

  This follows from the singleton lemma: `BareCanonicalCertificate` has exactly one element. -/
theorem adequate_route_certify_eq_canonical {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) (r : route.R) :
    route.certify r = canonicalBareCertificate :=
  bareCanonicalCertificate_unique (route.certify r)

/-- **T-UQ.3** — The compare-map of any adequate route always forgets to `canonicalBareCertificate`.

  By soundness, `certify r = forgetToBareCanonical (compare r)`, and by T-UQ.2,
  `certify r = canonicalBareCertificate`. -/
theorem adequate_route_compare_forgets_to_canonical {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) (r : route.R) :
    forgetToBareCanonical (route.compare r) = canonicalBareCertificate := by
  rw [← route.sound r]
  exact adequate_route_certify_eq_canonical route r

/-! ## T-UQ.4 — All adequate routes are extensionally equivalent -/

/-- **T-UQ.4** — Any two adequate routes are extensionally equivalent.

  Both certify the same bare object (`canonicalBareCertificate`) and both forget their
  comparison maps to the same bare object. Since any two elements of different carriers
  agree at the certification/forgetting level, any element of one carrier witnesses
  the extensional condition for any element of the other. -/
theorem adequate_routes_extensionally_equivalent {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n}
    (route₁ route₂ : AdequateReflectiveRoute BD n A) :
    RouteExtensionallyEquiv route₁ route₂ := by
  -- Both routes must be nonempty for the symmetric condition.
  -- We extract witnesses from the nondegeneracy condition (proper extension gives two elements).
  obtain ⟨x₁, _, _, _⟩ := route₁.nondegenerate
  obtain ⟨y₁, _, _, _⟩ := route₂.nondegenerate
  constructor
  · intro r₁
    refine ⟨y₁, ?_, ?_⟩
    · rw [adequate_route_certify_eq_canonical route₁, adequate_route_certify_eq_canonical route₂]
    · rw [adequate_route_compare_forgets_to_canonical route₁,
          adequate_route_compare_forgets_to_canonical route₂]
  · intro r₂
    refine ⟨x₁, ?_, ?_⟩
    · rw [adequate_route_certify_eq_canonical route₂, adequate_route_certify_eq_canonical route₁]
    · rw [adequate_route_compare_forgets_to_canonical route₂,
          adequate_route_compare_forgets_to_canonical route₁]

/-! ## T-UQ.1 — Extensional equivalence is an equivalence relation -/

theorem routeExtensionallyEquiv_refl {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route : AdequateReflectiveRoute BD n A) : RouteExtensionallyEquiv route route := by
  obtain ⟨x₁, _, _, _⟩ := route.nondegenerate
  exact ⟨fun r => ⟨x₁, by simp [adequate_route_certify_eq_canonical],
    by simp [adequate_route_compare_forgets_to_canonical]⟩,
    fun r => ⟨x₁, by simp [adequate_route_certify_eq_canonical],
      by simp [adequate_route_compare_forgets_to_canonical]⟩⟩

theorem routeExtensionallyEquiv_symm {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {route₁ route₂ : AdequateReflectiveRoute BD n A}
    (h : RouteExtensionallyEquiv route₁ route₂) : RouteExtensionallyEquiv route₂ route₁ :=
  ⟨fun r => by obtain ⟨r₁, h₁, h₂⟩ := h.2 r; exact ⟨r₁, h₁, h₂⟩,
   fun r => by obtain ⟨r₂, h₁, h₂⟩ := h.1 r; exact ⟨r₂, h₁, h₂⟩⟩

theorem routeExtensionallyEquiv_trans {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {route₁ route₂ route₃ : AdequateReflectiveRoute BD n A}
    (h₁₂ : RouteExtensionallyEquiv route₁ route₂)
    (h₂₃ : RouteExtensionallyEquiv route₂ route₃) :
    RouteExtensionallyEquiv route₁ route₃ :=
  adequate_routes_extensionally_equivalent route₁ route₃

/-! ## D-UQ.struct — Route Equivalence (structural) -/

/-- **D-UQ.struct** — Strong route equivalence: mutual route maps that are inverse up to
  certification behavior. This is the full structural notion; it is inhabited in `RouteUniqueness.lean`.

  Note: since `BareCanonicalCertificate` is a singleton, all certification maps are equal, so
  `fwd_bwd_certify_id` and `bwd_fwd_certify_id` hold automatically. The forward and backward maps
  just need to exist as route maps. -/
structure RouteEquiv {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (route₁ route₂ : AdequateReflectiveRoute BD n A) where
  fwd : RouteMap route₁ route₂
  bwd : RouteMap route₂ route₁
  fwd_bwd_certify_id : ∀ r : route₁.R,
    route₁.certify r = route₁.certify (bwd.toFun (fwd.toFun r))
  bwd_fwd_certify_id : ∀ r : route₂.R,
    route₂.certify r = route₂.certify (fwd.toFun (bwd.toFun r))

/-- `RouteEquiv` is inhabited whenever we have mutual route maps; the coherence conditions
  are automatic since all certifications are equal to `canonicalBareCertificate`. -/
def RouteEquiv.mk_of_maps {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {route₁ route₂ : AdequateReflectiveRoute BD n A}
    (fwd : RouteMap route₁ route₂) (bwd : RouteMap route₂ route₁) :
    RouteEquiv route₁ route₂ where
  fwd := fwd
  bwd := bwd
  fwd_bwd_certify_id := fun r => by
    rw [adequate_route_certify_eq_canonical route₁, adequate_route_certify_eq_canonical route₁]
  bwd_fwd_certify_id := fun r => by
    rw [adequate_route_certify_eq_canonical route₂, adequate_route_certify_eq_canonical route₂]

end InfinityCompression.MetaProof
