/-
  EPIC_009 — **fiber classification** of enriched reflective realizations over a fixed bare certificate.

  **D-FC.1** — `fiberAtBare` — preimage subtype of `forgetToBareCanonical` at `y`.

  **D-FC.2** — `roleOfSplit` — role-separated skeleton from an enriched split (`ReflectiveMirrorWitness.roles`).

  **D-FC.3** — `canonicalBareCertificate` — distinguished basepoint `admissibleStandard` as `BareCanonicalCertificate`.

  **D-FC.4** — `splitInCanonicalFiber` — embeds any standard `fromRolesAndExtraction_standard` witness into the fiber
  over `canonicalBareCertificate` (architecture-generic). `nemsSplitInCanonicalFiber` is the NEMS-typed alias.

  **T-FC.1a** — `enriched_reflective_split_forgets_to_canonical_bare_certificate` — every enriched split forgets to
  `canonicalBareCertificate`. **T-FC.1** (NEMS) is the flagship typed corollary.

  **T-FC.2** — Distinct roles ⇒ distinct enriched splits in the same fiber (via `fromRoles` + same `H`).

  **T-FC.3** — The fiber over `canonicalBareCertificate` on NEMS is **nontrivial** (≥ two points).

  **T-FC.4** — `nems_roles_injective_into_canonical_fiber` — role assignments inject into that fiber (partial classification).

  **scope:** No carrier redesign; organizes EPIC_008 `forgetToBareCanonical` into fiber language + NEMS role embedding.
-/

import InfinityCompression.MetaProof.ReflectiveRouteComparison

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-- **D-FC.1** — Fiber of `forgetToBareCanonical` over a bare certificate `y`. -/
def fiberAtBare {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n} (y : BareCanonicalCertificate) :=
  { x : EnrichedReflectiveSplit BD n A // forgetToBareCanonical x = y }

/-- **D-FC.2** — Extra structure tracked by the enriched route: role-separated poles. -/
def roleOfSplit {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (x : EnrichedReflectiveSplit BD n A) : RoleSeparatedSkeleton A :=
  x.val.roles

/-- **D-FC.3** — Canonical bare summit certificate (unique distinguished point in `BareCanonicalCertificate`). -/
def canonicalBareCertificate : BareCanonicalCertificate :=
  ⟨admissibleStandard, rfl⟩

/-- **T-FC.1a** — Any enriched reflective split forgets to the canonical bare certificate (Program C+ collapse). -/
theorem enriched_reflective_split_forgets_to_canonical_bare_certificate {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (x : EnrichedReflectiveSplit BD n A) :
    forgetToBareCanonical x = canonicalBareCertificate := by
  apply Subtype.ext
  exact reflective_split_forgets_to_canonical x

/-- **T-FC.1** — NEMS-typed corollary of **T-FC.1a** (flagship instance layer). -/
theorem nems_enriched_split_forgets_to_canonical_certificate
    (x : EnrichedReflectiveSplit _ _ nemsSpineChain.toArchitecture) :
    forgetToBareCanonical x = canonicalBareCertificate :=
  enriched_reflective_split_forgets_to_canonical_bare_certificate x

/-- **T-FC.3** — Nontrivial fiber over `canonicalBareCertificate` (repackages **T-DQ4.3** as fiber language). -/
theorem nems_fiber_over_canonical_nontrivial (H : SummitComponentExtraction nemsSpineChain.toArchitecture) :
    ∃ f₁ f₂ : fiberAtBare (BD := _) (n := _) (A := nemsSpineChain.toArchitecture) canonicalBareCertificate,
      f₁ ≠ f₂ := by
  obtain ⟨x₁, x₂, hne, _⟩ := nems_reflective_route_not_injective_to_bare H
  refine ⟨⟨x₁, enriched_reflective_split_forgets_to_canonical_bare_certificate x₁⟩,
    ⟨x₂, enriched_reflective_split_forgets_to_canonical_bare_certificate x₂⟩, ?_⟩
  intro heq
  exact hne (congrArg Subtype.val heq)

/-- **T-FC.2** — Distinct roles ⇒ distinct fiber points (standard `fromRoles` packaging, same `H`, same fiber). -/
theorem nems_distinct_roles_distinct_fiber_points
    (H : SummitComponentExtraction nemsSpineChain.toArchitecture)
    (roles₁ roles₂ : RoleSeparatedSkeleton nemsSpineChain.toArchitecture)
    (hs₁ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H))
    (hs₂ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H))
    (hne : roles₁ ≠ roles₂) :
    ∃ f₁ f₂ : fiberAtBare (BD := _) (n := _) (A := nemsSpineChain.toArchitecture) canonicalBareCertificate,
      f₁ ≠ f₂ ∧ roleOfSplit f₁.val = roles₁ ∧ roleOfSplit f₂.val = roles₂ := by
  let x₁ : EnrichedReflectiveSplit _ _ _ :=
    ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H, hs₁⟩
  let x₂ : EnrichedReflectiveSplit _ _ _ :=
    ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H, hs₂⟩
  refine ⟨⟨x₁, enriched_reflective_split_forgets_to_canonical_bare_certificate x₁⟩,
    ⟨x₂, enriched_reflective_split_forgets_to_canonical_bare_certificate x₂⟩, ?_, ?_, ?_⟩
  · intro heq
    have hm := congrArg Subtype.val (congrArg Subtype.val heq)
    have hr := reflective_mirror_from_roles_injective_roles roles₁ roles₂ H hm
    exact absurd hr hne
  · rfl
  · rfl

/-- **D-FC.4** — Embed `(roles, H)` into the fiber over `canonicalBareCertificate` (any architecture). -/
def splitInCanonicalFiber {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A) (roles : RoleSeparatedSkeleton A)
    (hs : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H)) :
    fiberAtBare (BD := _) (n := _) (A := A) canonicalBareCertificate :=
  ⟨⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H, hs⟩,
    enriched_reflective_split_forgets_to_canonical_bare_certificate _⟩

/-- NEMS-typed alias of `splitInCanonicalFiber` (concrete flagship spine). -/
def nemsSplitInCanonicalFiber (H : SummitComponentExtraction nemsSpineChain.toArchitecture)
    (roles : RoleSeparatedSkeleton nemsSpineChain.toArchitecture)
    (hs : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H)) :
    fiberAtBare (BD := _) (n := _) (A := nemsSpineChain.toArchitecture) canonicalBareCertificate :=
  splitInCanonicalFiber H roles hs

/-- **T-FC.4** (general) — Roles inject into the canonical fiber along `splitInCanonicalFiber`. -/
theorem splitInCanonicalFiber_roles_injective {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    (H : SummitComponentExtraction A) (roles₁ roles₂ : RoleSeparatedSkeleton A)
    (hs₁ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H))
    (hs₂ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H)) :
    splitInCanonicalFiber H roles₁ hs₁ = splitInCanonicalFiber H roles₂ hs₂ → roles₁ = roles₂ := by
  intro heq
  refine reflective_mirror_from_roles_injective_roles roles₁ roles₂ H ?_
  exact congrArg Subtype.val (congrArg Subtype.val heq)

/-- **T-FC.4** — NEMS-named corollary of `splitInCanonicalFiber_roles_injective`. -/
theorem nems_roles_injective_into_canonical_fiber (H : SummitComponentExtraction nemsSpineChain.toArchitecture)
    (roles₁ roles₂ : RoleSeparatedSkeleton nemsSpineChain.toArchitecture)
    (hs₁ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H))
    (hs₂ : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H)) :
    nemsSplitInCanonicalFiber H roles₁ hs₁ = nemsSplitInCanonicalFiber H roles₂ hs₂ → roles₁ = roles₂ :=
  splitInCanonicalFiber_roles_injective H roles₁ roles₂ hs₁ hs₂

/-- **T-FC.4** (surjective-on-subfamily wording) — `roleOfSplit` composed with the canonical-fiber embedding recovers `roles`. -/
theorem nems_roleOfSplit_nemsSplitInCanonicalFiber (H : SummitComponentExtraction nemsSpineChain.toArchitecture)
    (roles : RoleSeparatedSkeleton nemsSpineChain.toArchitecture)
    (hs : ReflectiveSplitAutonomous (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H)) :
    roleOfSplit (nemsSplitInCanonicalFiber H roles hs).val = roles := by
  rfl

end InfinityCompression.MetaProof
