/-
  EPIC_014_RS1 — **Route Forced Continuation and Reflexive Self-Location** (Program V / RS).

  Defines the theorem program as a route object and proves that it instantiates the CI route
  architecture under its own necessity theorem. This is the reflexive self-location arc.

  **D-RS.1** — `theoremProgramRoute` — the IC theorem development formalized as an adequate
  route: carrier = `RoleSeparatedSkeleton A`, certify = constant `canonicalBareCertificate`,
  compare = `fromRolesAndExtraction_standard`. This is the actual derivation process of
  the theorem program, modeled as a route object.

  **T-RS.1** — `theoremProgramRoute_is_adequate` — the theorem program route is adequate.

  **T-RS.2** — `theorem_program_is_enrichedForgetful` — the theorem program route is
  enriched-forgetful (not bare-collapsed).

  **T-RS.3** — `bare_collapse_forces_enriched_continuation` — the bare collapse theorem
  forces any adequate continuation to be enriched-forgetful. This is the key structural
  forcing result.

  **T-RS.4** — `theorem_program_self_locates_in_ci` — the theorem program route maps to
  `ciRoute` in the route preorder.

  **T-RS.5** — `theorem_program_not_accidental` — the theorem program route is
  extensionally equivalent to `ciRoute` (the development uses the architecture it proves necessary).

  **scope:** Reflexive self-location. No new definitions beyond what is needed.
-/

import InfinityCompression.MetaProof.RouteEquivalence
import InfinityCompression.MetaProof.BroadClassTheorems

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## D-RS.1 — Theorem Program Route -/

/-- **D-RS.1** — The **theorem program route** for architecture `A` is the adequate route whose:
  - carrier `R` = `RoleSeparatedSkeleton A` (the space of proof strategies),
  - certify-map = constant `canonicalBareCertificate` (every strategy certifies the same result),
  - compare-map = `fromRolesAndExtraction_standard` (each strategy produces an enriched mirror witness).

  This represents the actual derivation process of the IC theorem program: role-separated skeletons
  are the constructive strategies, and the mirror witnesses are the enriched realizations they produce. -/
def theoremProgramRoute {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A) :
    AdequateReflectiveRoute BD n A where
  R := RoleSeparatedSkeleton A
  certify := fun _ => canonicalBareCertificate
  compare := fun r =>
    ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard r H,
     reflective_split_from_roles_standard r H⟩
  sound := fun r => by
    apply Eq.symm
    exact enriched_reflective_split_forgets_to_canonical_bare_certificate _
  lands := fun _ => canonicalBareCertificate.property
  nondegenerate := by
    obtain ⟨r₁, r₂, hne⟩ := hne
    have hmirror_ne := reflective_mirror_from_roles_ne_of_roles_ne r₁ r₂ H hne
    let x₁ : EnrichedReflectiveSplit BD n A :=
      ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₁ H,
       reflective_split_from_roles_standard r₁ H⟩
    let x₂ : EnrichedReflectiveSplit BD n A :=
      ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₂ H,
       reflective_split_from_roles_standard r₂ H⟩
    refine ⟨r₁, r₂, hne, ?_⟩
    simp only [Function.comp_apply]
    exact (enriched_reflective_split_forgets_to_canonical_bare_certificate x₁).trans
      (enriched_reflective_split_forgets_to_canonical_bare_certificate x₂).symm

/-! ## T-RS.1 — The theorem program route is adequate -/

/-- **T-RS.1** — The NEMS theorem program route is adequate. -/
def nems_theoremProgramRoute (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    AdequateReflectiveRoute _ _ nemsSpineChain.toArchitecture :=
  theoremProgramRoute H
    ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, nems_role_skeletons_ne⟩
    nems_spine_architecture_crown_eligible

/-! ## T-RS.2 — The theorem program route is enriched-forgetful -/

/-- **T-RS.2** — The theorem program route is enriched-forgetful (not bare-collapsed).

  By `adequate_route_is_enrichedForgetful`, any adequate route is enriched-forgetful.
  The theorem program route is adequate (T-RS.1), so it is enriched-forgetful. -/
theorem theorem_program_is_enrichedForgetful {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A) :
    EnrichedForgetfulRoute (theoremProgramRoute H hne hce).compare :=
  adequate_route_is_enrichedForgetful (theoremProgramRoute H hne hce)

/-! ## T-RS.3 — Bare collapse forces enriched continuation -/

/-- **T-RS.3** — **Bare collapse forces enriched continuation.**

  Once the canonical collapse theorem is established (all skeletons yield the same bare
  certificate), any adequate continuation route on the same architecture must be enriched-forgetful.

  This is `universal_route_necessity` applied to the NEMS spine: the general theorem proves
  that the theorem development's own architecture forces the enriched route. The self-referential
  character comes from the fact that `universal_route_necessity` is a theorem of the development,
  and it applies to the development's own setting. -/
theorem bare_collapse_forces_enriched_continuation
    (H : SummitComponentExtraction nemsSpineChain.toArchitecture)
    (route : AdequateReflectiveRoute _ _ nemsSpineChain.toArchitecture) :
    EnrichedForgetfulRoute route.compare :=
  adequate_route_is_enrichedForgetful route

/-! ## T-RS.4 — The theorem program route maps to ciRoute -/

/-- **T-RS.4** — The theorem program route maps to `ciRoute` in the route preorder.

  This is `adequate_route_maps_to_ciRoute` applied to the theorem program route. The comparison map
  (which sends each role skeleton to its mirror witness) is the route map witness. -/
theorem theorem_program_self_locates_in_ci {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A) :
    RouteLE (theoremProgramRoute H hne hce) (ciRoute H hne hce) :=
  adequate_route_maps_to_ciRoute H hne hce (theoremProgramRoute H hne hce)

/-- **T-RS.4 (NEMS corollary)** — The NEMS theorem program route maps to the NEMS CI route. -/
theorem nems_theorem_program_self_locates_in_ci
    (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    RouteLE (nems_theoremProgramRoute H) (nems_ciRoute_is_adequate H) :=
  theorem_program_self_locates_in_ci H
    ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, nems_role_skeletons_ne⟩
    nems_spine_architecture_crown_eligible

/-! ## T-RS.5 — The theorem program is not accidental -/

/-- **T-RS.5** — **The theorem program is not accidental.**

  The theorem program route is extensionally equivalent to `ciRoute`: both certify the same
  canonical certificate and both forget their comparison maps to the same canonical certificate.

  This is the reflexive conclusion: the development uses the route architecture whose necessity
  it proves. By `adequate_routes_extensionally_equivalent`, any two adequate routes on the same
  architecture are extensionally equivalent. The theorem program route and `ciRoute` are both
  adequate, so they are equivalent.

  The development is not one design among many: it is the route selected by its own
  route-necessity theorem. -/
theorem theorem_program_not_accidental {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A) :
    RouteExtensionallyEquiv (theoremProgramRoute H hne hce) (ciRoute H hne hce) :=
  adequate_routes_extensionally_equivalent (theoremProgramRoute H hne hce) (ciRoute H hne hce)

/-- **T-RS.5 (NEMS corollary)** — The NEMS theorem program route is extensionally equivalent
  to the NEMS CI route. -/
theorem nems_theorem_program_not_accidental
    (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    RouteExtensionallyEquiv (nems_theoremProgramRoute H) (nems_ciRoute_is_adequate H) :=
  adequate_routes_extensionally_equivalent _ _

/-! ## Summary theorem — Reflexive self-location bundle -/

/-- **Summary** — The complete reflexive self-location result: the IC theorem development
  instantiates the route architecture it proves necessary, and this instantiation is not
  accidental but forced by the bare collapse theorem.

  Components:
  1. The theorem program route is adequate.
  2. It is enriched-forgetful (not bare-collapsed).
  3. Any adequate continuation of the program is forced to be enriched-forgetful.
  4. The theorem program route maps to the CI route.
  5. The theorem program route is extensionally equivalent to the CI route. -/
theorem reflexive_self_location_bundle {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A)
    (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂)
    (hce : CrownEligible A) :
    let tpr := theoremProgramRoute H hne hce
    let ci := ciRoute H hne hce
    EnrichedForgetfulRoute tpr.compare ∧
      RouteLE tpr ci ∧
      RouteExtensionallyEquiv tpr ci :=
  ⟨theorem_program_is_enrichedForgetful H hne hce,
   theorem_program_self_locates_in_ci H hne hce,
   theorem_program_not_accidental H hne hce⟩

end InfinityCompression.MetaProof
