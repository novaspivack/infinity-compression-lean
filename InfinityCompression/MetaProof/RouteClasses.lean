/-
  EPIC_011_UR1 — **Route Classes** (Program U, Module 2).

  Defines the three structurally distinct route classes and proves membership predicates.
  Every route falls into at least one class; adequate routes fall into exactly `EnrichedForgetfulRoute`.

  **D-U.4** — `BareCollapsedRoute` — a route whose comparison map is injective into the bare layer.
  These routes do not carry enriched realization data that survives forgetting.

  **D-U.5** — `EnrichedForgetfulRoute` — a route whose comparison map is a proper extension
  (non-injective into the bare layer). The CI route belongs to this class.

  **D-U.6** — `InadequateRoute` — a route that fails at least one adequacy condition.

  **T-U1.1** — `bareCollapsed_or_enrichedForgetful` — every route is either bare-collapsed or enriched-forgetful
  (classical dichotomy on injectivity).

  **T-U1.2** — `enrichedForgetfulRoute_iff_nondegenerate` — EnrichedForgetfulRoute and RouteNondegeneracy coincide.

  **T-U1.3** — `ciRoute_is_enrichedForgetful` — the CI route belongs to EnrichedForgetfulRoute.

  **scope:** Route class definitions and membership only. Necessity and minimality proofs are in
  `RouteNecessity.lean` and `RouteMinimality.lean`.
-/

import InfinityCompression.MetaProof.RouteAdequacy

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-! ## D-U.4 — Bare-Collapsed Route -/

/-- **D-U.4** — A route is **bare-collapsed** if its comparison map is injective into the bare layer:
  distinct elements of `R` produce distinct bare certificates after forgetting.

  Equivalently, `forgetToBareCanonical ∘ compare` is injective.

  A bare-collapsed route carries no enriched information that outlives the forgetful collapse. -/
def BareCollapsedRoute {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n} {R : Type}
    (compare : R → EnrichedReflectiveSplit BD n A) : Prop :=
  Function.Injective (forgetToBareCanonical ∘ compare)

/-! ## D-U.5 — Enriched Forgetful Route -/

/-- **D-U.5** — A route is **enriched-forgetful** if its comparison map is a proper extension
  (non-injective into the bare layer): there exist distinct route elements that produce the same
  bare certificate after forgetting, but distinct enriched splits.

  This is exactly `RouteNondegeneracy`. The CI route belongs to this class. -/
def EnrichedForgetfulRoute {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n} {R : Type}
    (compare : R → EnrichedReflectiveSplit BD n A) : Prop :=
  RouteNondegeneracy compare

/-! ## D-U.6 — Inadequate Route -/

/-- **D-U.6** — A route is **inadequate** if it fails at least one adequacy condition:
  soundness, canonical landing, or nondegeneracy.

  Note: this is the complement of `AdequateReflectiveRoute` at the predicate level. -/
def InadequateRoute {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n} {R : Type}
    (certify : R → BareCanonicalCertificate) (compare : R → EnrichedReflectiveSplit BD n A) : Prop :=
  ¬ (RouteSoundness certify compare ∧ RouteCanonicalLanding certify ∧ RouteNondegeneracy compare)

/-! ## T-U1.1 — Bare-collapsed / enriched-forgetful dichotomy -/

/-- **T-U1.1** — Every route is either bare-collapsed or enriched-forgetful (classical dichotomy).

  This follows immediately from the law of excluded middle applied to `Function.Injective`. -/
theorem bareCollapsed_or_enrichedForgetful {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {R : Type} (compare : R → EnrichedReflectiveSplit BD n A) :
    BareCollapsedRoute compare ∨ EnrichedForgetfulRoute compare := by
  by_cases h : Function.Injective (forgetToBareCanonical ∘ compare)
  · left; exact h
  · right
    simp only [EnrichedForgetfulRoute, RouteNondegeneracy, ProperExtensionViaForgetful,
      Function.Injective] at *
    push_neg at h
    obtain ⟨a₁, a₂, heq, hne⟩ := h
    exact ⟨a₁, a₂, hne, heq⟩

/-! ## T-U1.2 — EnrichedForgetfulRoute ↔ RouteNondegeneracy -/

/-- **T-U1.2** — `EnrichedForgetfulRoute` and `RouteNondegeneracy` are definitionally equivalent. -/
theorem enrichedForgetfulRoute_iff_nondegenerate {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {R : Type} (compare : R → EnrichedReflectiveSplit BD n A) :
    EnrichedForgetfulRoute compare ↔ RouteNondegeneracy compare :=
  Iff.rfl

/-! ## T-U1.3 — CI route is enriched-forgetful -/

/-- **T-U1.3** — The CI route (carrier = `EnrichedReflectiveSplit`, compare = id) is enriched-forgetful,
  given the existence of two distinct role-separated skeletons. -/
theorem ciRoute_is_enrichedForgetful {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A) (hne : ∃ r₁ r₂ : RoleSeparatedSkeleton A, r₁ ≠ r₂) :
    EnrichedForgetfulRoute (id (α := EnrichedReflectiveSplit BD n A)) := by
  simp only [EnrichedForgetfulRoute, RouteNondegeneracy, ProperExtensionViaForgetful,
    Function.comp_id]
  obtain ⟨r₁, r₂, hne⟩ := hne
  let m₁ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₁ H
  let m₂ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₂ H
  have hs₁ := reflective_split_from_roles_standard r₁ H
  have hs₂ := reflective_split_from_roles_standard r₂ H
  refine ⟨⟨m₁, hs₁⟩, ⟨m₂, hs₂⟩, ?_, ?_⟩
  · exact enriched_reflective_split_ne_of_witness_ne _ _
      (reflective_mirror_from_roles_ne_of_roles_ne r₁ r₂ H hne)
  · exact forgetToBareCanonical_eq_of_bridge_derivation_eq _ _
      ((skeleton_indexed_fromRoles_derivation_eq_admissibleStandard r₁ H).trans
        (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard r₂ H).symm)

/-- **T-U1.3** (NEMS corollary) — The NEMS CI route is enriched-forgetful. -/
theorem nems_ciRoute_is_enrichedForgetful (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    EnrichedForgetfulRoute (id (α := EnrichedReflectiveSplit _ _ nemsSpineChain.toArchitecture)) :=
  ciRoute_is_enrichedForgetful H ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, nems_role_skeletons_ne⟩

end InfinityCompression.MetaProof
