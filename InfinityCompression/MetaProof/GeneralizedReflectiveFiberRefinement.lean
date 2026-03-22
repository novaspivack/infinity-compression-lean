/-
  EPIC_010 — **generalized reflective fiber refinement** (role-rich / role-pair-diverse crown classes).

  **D-GR.1** — `RoleRichCrownEligible` — `CrownEligible` + **nonempty** `RoleSeparatedSkeleton` (honest first abstraction).

  **D-GR.2** — `RolePairDiverseCrownEligible` — `CrownEligible` + **two** distinct role-separated skeletons (hypothesis for
  strict refinement / non-injective forgetting on a general architecture).

  **T-GR.1** — Existence of enriched reflective splits from `RoleRichCrownEligible` + `SummitComponentExtraction`.

  **T-GR.2** — Constructed / arbitrary enriched splits forget to `canonicalBareCertificate` (via **T-FC.1a**).

  **T-GR.3** — `RolePairDiverseCrownEligible` ⇒ **strict refinement** (distinct enriched splits, same bare certificate).

  **T-GR.4** — `ProperExtensionViaForgetful` for `forgetToBareCanonical` under **T-GR.3**.

  **T-GR.5** — `generalized_role_injection_into_canonical_fiber` — alias layer for **T-FC.4** `splitInCanonicalFiber_roles_injective`.

  **T-GR.6** — NEMS instance theorems for **T-GR.3**-style conclusion.

  **T-GR.7** — `nems_spine_role_rich_crown_eligible`, `nems_spine_role_pair_diverse_crown_eligible`.

  **scope:** Additive over EPIC_009 — NEMS flagship theorems remain in `ReflectiveFiberClassification.lean`; this file is the
  law layer for broader architectures.
-/

import InfinityCompression.MetaProof.CrownEligible
import InfinityCompression.MetaProof.NonPackagingConstruction
import InfinityCompression.MetaProof.ReflectiveFiberClassification
import InfinityCompression.MetaProof.ReflectiveMirrorWitness
import InfinityCompression.MetaProof.ReflectiveSplit
import InfinityCompression.MetaProof.RoleSeparatedSkeleton
import InfinityCompression.MetaProof.SkeletonIndexedExtractionBridge

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-- **D-GR.1** — Crown-eligible + **some** role-separated skeleton (standard constructive interface available). -/
def RoleRichCrownEligible {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) : Prop :=
  CrownEligible A ∧ Nonempty (RoleSeparatedSkeleton A)

/-- **D-GR.2** — Crown-eligible + **two** distinct role-separated skeletons (enables strict refinement of the forgetful map). -/
def RolePairDiverseCrownEligible {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) : Prop :=
  CrownEligible A ∧ ∃ (r₁ r₂ : RoleSeparatedSkeleton A), r₁ ≠ r₂

/-- **T-GR.7a** — Canonical NEMS spine is **role-rich** crown-eligible. -/
theorem nems_spine_role_rich_crown_eligible : RoleRichCrownEligible nemsSpineChain.toArchitecture :=
  ⟨nems_spine_architecture_crown_eligible, nems_spine_nonempty_role_separated_skeleton⟩

/-- **T-GR.7b** — Canonical NEMS spine is **role-pair-diverse** crown-eligible. -/
theorem nems_spine_role_pair_diverse_crown_eligible : RolePairDiverseCrownEligible nemsSpineChain.toArchitecture :=
  ⟨nems_spine_architecture_crown_eligible, ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, nems_role_skeletons_ne⟩⟩

/-- **T-GR.1** — From `RoleRichCrownEligible` + extraction, obtain an enriched reflective split. -/
theorem role_rich_crown_eligible_obtains_enriched_reflective_split {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (h : RoleRichCrownEligible A) (H : SummitComponentExtraction A) :
    ∃ x : EnrichedReflectiveSplit BD n A, ReflectiveSplitAutonomous x.val := by
  cases h.2 with
  | intro roles =>
    let x : EnrichedReflectiveSplit BD n A :=
      ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H,
        reflective_split_from_roles_standard roles H⟩
    exact ⟨x, x.property⟩

/-- **T-GR.1** — Nonempty carrier of enriched splits (corollary). -/
theorem role_rich_crown_eligible_nonempty_enriched_split {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (h : RoleRichCrownEligible A) (H : SummitComponentExtraction A) :
    Nonempty (EnrichedReflectiveSplit BD n A) := by
  cases h.2 with
  | intro roles =>
    exact Nonempty.intro ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H,
      reflective_split_from_roles_standard roles H⟩

/-- **T-GR.2** — Standard `fromRoles` splits forget to `canonicalBareCertificate` (uses **T-FC.1a**). -/
theorem from_roles_standard_forgets_to_canonical_bare_certificate {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (roles : RoleSeparatedSkeleton A) (H : SummitComponentExtraction A)
    (hs : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H)) :
    forgetToBareCanonical ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H, hs⟩ =
      canonicalBareCertificate :=
  enriched_reflective_split_forgets_to_canonical_bare_certificate _

/-- **T-GR.3** — Strict refinement: two distinct role skeletons + shared extraction ⇒ distinct enriched splits, same forget. -/
theorem role_pair_diverse_crown_eligible_strict_refinement {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (h : RolePairDiverseCrownEligible A) (H : SummitComponentExtraction A) :
    ∃ x₁ x₂ : EnrichedReflectiveSplit BD n A,
      x₁ ≠ x₂ ∧ forgetToBareCanonical x₁ = forgetToBareCanonical x₂ := by
  rcases h.2 with ⟨r₁, r₂, hne⟩
  have hs₁ := reflective_split_from_roles_standard r₁ H
  have hs₂ := reflective_split_from_roles_standard r₂ H
  refine ⟨⟨_, hs₁⟩, ⟨_, hs₂⟩, ?_, ?_⟩
  · exact enriched_reflective_split_ne_of_witness_ne _ _
      (reflective_mirror_from_roles_ne_of_roles_ne r₁ r₂ H hne)
  · exact forgetToBareCanonical_eq_of_bridge_derivation_eq _ _
      ((skeleton_indexed_fromRoles_derivation_eq_admissibleStandard r₁ H).trans
        (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard r₂ H).symm)

/-- **T-GR.4** — Proper extension of the bare route (same phenomenon as **T-DQ4.4**, architecture-generic hypothesis). -/
theorem role_pair_diverse_crown_eligible_proper_extension_forget {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (h : RolePairDiverseCrownEligible A) (H : SummitComponentExtraction A) :
    ProperExtensionViaForgetful (forgetToBareCanonical (BD := _) (n := _) (A := A)) := by
  obtain ⟨x₁, x₂, hne, heq⟩ := role_pair_diverse_crown_eligible_strict_refinement h H
  exact ⟨x₁, x₂, hne, heq⟩

/-- **T-GR.5** — Role injection into the canonical fiber (restatement of **T-FC.4** general for EPIC_010 narrative). -/
theorem generalized_role_injection_into_canonical_fiber {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A) (r₁ r₂ : RoleSeparatedSkeleton A)
    (hs₁ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₁ H))
    (hs₂ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₂ H)) :
    splitInCanonicalFiber H r₁ hs₁ = splitInCanonicalFiber H r₂ hs₂ → r₁ = r₂ :=
  splitInCanonicalFiber_roles_injective H r₁ r₂ hs₁ hs₂

/-- **T-GR.6** — NEMS satisfies **T-GR.3** / **T-GR.4** via `nems_spine_role_pair_diverse_crown_eligible`. -/
theorem nems_role_pair_diverse_strict_refinement (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ∃ x₁ x₂ : EnrichedReflectiveSplit _ _ nemsSpineChain.toArchitecture,
      x₁ ≠ x₂ ∧ forgetToBareCanonical x₁ = forgetToBareCanonical x₂ :=
  role_pair_diverse_crown_eligible_strict_refinement nems_spine_role_pair_diverse_crown_eligible H

end InfinityCompression.MetaProof
