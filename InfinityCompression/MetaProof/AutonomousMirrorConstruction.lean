/-
  EPIC_007_AS1 — **autonomous mirror construction** theorems (post-summit layer).

  **T-F1.1** — `autonomous_mirror_from_roles_extraction_standard` — see `ReflectiveMirrorWitness.lean`.

  **T-F1.2** — `nems_spine_autonomous_mirror_ingredients` — canonical spine carries **role** data + extraction.

  **T-F1.3** — `crown_eligible_constructs_autonomous_mirror_of_role_skeleton` — given **explicit**
  `RoleSeparatedSkeleton` + `SummitComponentExtraction`, build `AutonomousSummitMirror`.

  **T-F1.4** — `nems_spine_autonomous_mirror` — flagship **NEMS spine** instance.

  **T-F1.5** — `nonempty_role_skeleton_yields_autonomous_mirror` — `Nonempty (RoleSeparatedSkeleton A)` is
  sufficient (covers every architecture that **admits** a role-separated skeleton).

  **scope / honesty:** `librarySummitExtraction` is the default `H` in spine examples — same **shard lemma**
  class as **T-P3.5c**; the **new** content is the **ReflectiveMirrorWitness** carrier + explicit
  `fromRolesExtraction` chain. A future skeleton-dependent `SummitComponentExtraction` is the real
  epistemic upgrade over **T-P2.7**.

  See `specs/IN-PROCESS/EPIC_007_AS1_SUMMIT_INDEPENDENT_REFLECTIVE_MIRROR_SPEC.md`.
-/

import InfinityCompression.MetaProof.CrownEligible
import InfinityCompression.MetaProof.NonPackagingConstruction
import InfinityCompression.MetaProof.ReflectiveMirrorWitness
import InfinityCompression.MetaProof.RoleSeparatedSkeleton

import InfinityCompression.Meta.NEMSSpineAsArchitecture

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Meta

/-- **T-F1.2** — NEMS spine has **role-separated** skeleton data and a **SummitComponentExtraction**. -/
theorem nems_spine_autonomous_mirror_ingredients :
    Nonempty (RoleSeparatedSkeleton nemsSpineChain.toArchitecture) ∧
      Nonempty (SummitComponentExtraction nemsSpineChain.toArchitecture) :=
  ⟨nems_spine_nonempty_role_separated_skeleton, Nonempty.intro (librarySummitExtraction _)⟩

/-- **T-F1.3** — From crown eligibility **and** an explicit role-separated skeleton + extraction. -/
theorem crown_eligible_constructs_autonomous_mirror_of_role_skeleton {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (_h : CrownEligible A) (roles : RoleSeparatedSkeleton A)
    (H : SummitComponentExtraction A) :
    ∃ m : ReflectiveMirrorWitness A, AutonomousSummitMirror m :=
  ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H,
    autonomous_mirror_from_roles_extraction_standard roles H⟩

/-- **T-F1.5** — `Nonempty (RoleSeparatedSkeleton A)` + extraction ⇒ autonomous mirror. -/
theorem nonempty_role_skeleton_yields_autonomous_mirror {BD : Type u} {n : Nat}
    {A : CompressionArchitecture BD n} (hne : Nonempty (RoleSeparatedSkeleton A))
    (H : SummitComponentExtraction A) :
    ∃ m : ReflectiveMirrorWitness A, AutonomousSummitMirror m := by
  cases hne with
  | intro roles =>
    exact ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles H,
      autonomous_mirror_from_roles_extraction_standard roles H⟩

/-- **T-F1.4** — Canonical **NEMS spine** autonomous mirror (flagship instance). -/
theorem nems_spine_autonomous_mirror :
    ∃ m : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
      AutonomousSummitMirror m :=
  ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard nemsRoleSkeleton_1_0 (librarySummitExtraction _),
    autonomous_mirror_from_roles_extraction_standard _ _⟩

end InfinityCompression.MetaProof
