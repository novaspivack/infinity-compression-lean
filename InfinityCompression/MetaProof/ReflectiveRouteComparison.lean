/-
  EPIC_008_DQ4 — **reflective route comparison and dominance** (forgetful map + proper extension).

  **D-DQ4.1** — `BareCanonicalCertificate` — subtype of `AdmissibleSummitDerivation` with
  `IsCanonicalBareSummitCertification`.

  **D-DQ4.2** — `EnrichedReflectiveSplit` — subtype of `ReflectiveMirrorWitness` satisfying
  `ReflectiveSplitAutonomous`.

  **D-DQ4.3** — `forgetToBareCanonical` — forgetful map to the bare canonical certificate.

  **D-DQ4.4** — `ProperExtensionViaForgetful` — ∃ distinct domain points with equal image (non-injective ⇒
  proper extension over the bare class).

  **T-DQ4.1** — `reflective_split_forgets_to_canonical` — no-loss to `IsCanonicalBareSummitCertification`.

  **T-DQ4.2** — `forgetToBareCanonical_sound` — alignment with `bridge.derivation` via `Subtype`.

  **T-DQ4.3** — `nems_reflective_route_not_injective_to_bare` — two distinct enriched splits, same forgetful image.

  **T-DQ4.4** — `nems_reflective_route_strictly_refines_bare` — `ProperExtensionViaForgetful` on NEMS.

  **scope:** No carrier redesign — comparison only on existing Program C+ objects.
-/

import InfinityCompression.MetaProof.CanonicalCertification
import InfinityCompression.MetaProof.ReflectiveMirrorWitness
import InfinityCompression.MetaProof.ReflectiveSplit
import InfinityCompression.MetaProof.RoleSeparatedSkeleton
import InfinityCompression.MetaProof.SkeletonIndexedExtractionBridge

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-- **D-DQ4.1** — Bare summit route as a **typed** certificate (subtype for clean equality from derivation). -/
abbrev BareCanonicalCertificate : Type :=
  { d : AdmissibleSummitDerivation // IsCanonicalBareSummitCertification d }

/-- **D-DQ4.2** — Enriched reflective route as object. -/
abbrev EnrichedReflectiveSplit (BD : Type u) (n : Nat) (A : CompressionArchitecture BD n) :=
  { m : ReflectiveMirrorWitness A // ReflectiveSplitAutonomous m }

/-- **D-DQ4.3** — Forgetful map: enriched split ⇒ bare canonical certificate. -/
def forgetToBareCanonical {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x : EnrichedReflectiveSplit BD n A) : BareCanonicalCertificate :=
  ⟨x.val.bridge.derivation, x.property.1⟩

/-- **D-DQ4.4** — `f` is a **proper extension** (non-injective): distinct inputs, same output. -/
def ProperExtensionViaForgetful {α β : Sort*} (f : α → β) : Prop :=
  ∃ x₁ x₂ : α, x₁ ≠ x₂ ∧ f x₁ = f x₂

theorem enriched_reflective_split_ne_of_witness_ne {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x₁ x₂ : EnrichedReflectiveSplit BD n A) (h : x₁.val ≠ x₂.val) : x₁ ≠ x₂ := fun heq =>
  h (congrArg Subtype.val heq)

/-- **T-DQ4.1** — No-loss: enriched split forgets to a canonical bare certification. -/
theorem reflective_split_forgets_to_canonical {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x : EnrichedReflectiveSplit BD n A) : IsCanonicalBareSummitCertification x.val.bridge.derivation :=
  x.property.1

/-- **T-DQ4.2** — Soundness: forgetful projection is `bridge.derivation`, with canonical proof. -/
theorem forgetToBareCanonical_sound {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x : EnrichedReflectiveSplit BD n A) :
    (forgetToBareCanonical x).val = x.val.bridge.derivation ∧
      IsCanonicalBareSummitCertification (forgetToBareCanonical x).val :=
  ⟨rfl, (forgetToBareCanonical x).property⟩

theorem forgetToBareCanonical_eq_of_bridge_derivation_eq {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x₁ x₂ : EnrichedReflectiveSplit BD n A)
    (h : x₁.val.bridge.derivation = x₂.val.bridge.derivation) : forgetToBareCanonical x₁ = forgetToBareCanonical x₂ :=
  Subtype.ext h

/-- **T-DQ4.3** — On NEMS, the forgetful map is **not** injective. -/
theorem nems_reflective_route_not_injective_to_bare (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ∃ x₁ x₂ : EnrichedReflectiveSplit _ _ nemsSpineChain.toArchitecture,
      x₁ ≠ x₂ ∧ forgetToBareCanonical x₁ = forgetToBareCanonical x₂ := by
  let m₁ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_1_0 H
  let m₂ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_3_2 H
  have hs₁ : ReflectiveSplitAutonomous m₁ := reflective_split_from_roles_standard nemsRoleSkeleton_1_0 H
  have hs₂ : ReflectiveSplitAutonomous m₂ := reflective_split_from_roles_standard nemsRoleSkeleton_3_2 H
  refine ⟨⟨m₁, hs₁⟩, ⟨m₂, hs₂⟩, ?_, ?_⟩
  · exact enriched_reflective_split_ne_of_witness_ne _ _
      (reflective_mirror_from_roles_ne_of_roles_ne nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2 H nems_role_skeletons_ne)
  · exact forgetToBareCanonical_eq_of_bridge_derivation_eq _ _
      ((skeleton_indexed_fromRoles_derivation_eq_admissibleStandard nemsRoleSkeleton_1_0 H).trans
        (skeleton_indexed_fromRoles_derivation_eq_admissibleStandard nemsRoleSkeleton_3_2 H).symm)

/-- **T-DQ4.4** — Strict refinement / proper extension on the canonical NEMS spine. -/
theorem nems_reflective_route_strictly_refines_bare (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ProperExtensionViaForgetful (forgetToBareCanonical (BD := _) (n := _) (A := nemsSpineChain.toArchitecture)) := by
  obtain ⟨x₁, x₂, hne, heq⟩ := nems_reflective_route_not_injective_to_bare H
  exact ⟨x₁, x₂, hne, heq⟩

/-- Alias (**T-DQ4.4**). -/
theorem nems_reflective_route_properly_refines_bare (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ProperExtensionViaForgetful (forgetToBareCanonical (BD := _) (n := _) (A := nemsSpineChain.toArchitecture)) :=
  nems_reflective_route_strictly_refines_bare H

end InfinityCompression.MetaProof
