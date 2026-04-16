/-
  EPIC_004_PM3 — **Phase 1:** non-packaging correspondence **target** (Route B post–B-009).

  **D-P1.1** / **T-P1.1** pin the nv32 mirror site to an explicit `Fin n` index (architecture-observable),
  strengthening the abstract `∃ i` in `MirrorsArchitecture` to a **chosen** witness.

  **scope: structural bookkeeping** — witnesses for `admissibleStandard` are still the library summit
  proofs; the advance vs B-007 is **explicit pinning**, not independence from `admissibleStandard`.
  **Phase 2** (separate) aims for a derivation not mediated by that package.
-/

import InfinityCompression.MetaProof.AdmissibleDerivations
import InfinityCompression.MetaProof.ArchitectureDerivationCorrespondence
import InfinityCompression.MetaProof.CrownEligible

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Core
open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-P1.1** — Mirror **pinned** at index `i`: same conjuncts as `MirrorsArchitecture` except the
  nv32 site is the **given** `i`, not an anonymous existential. -/
def PinnedMirrorsArchitecture {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)
    (d : AdmissibleSummitDerivation) (i : Fin n) : Prop :=
  interpretSummitBundle d.bundle ∧
    RecordsDependencyShape d dependencyShapeStandard ∧
      (A.nodes i).profile = nv32InductionProfile

theorem mirrorsArchitecture_of_pinned {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {d : AdmissibleSummitDerivation} {i : Fin n} (hp : PinnedMirrorsArchitecture A d i) :
    MirrorsArchitecture A d :=
  ⟨hp.1, hp.2.1, ⟨i, hp.2.2⟩⟩

/-- **T-P1.1** — Crown-eligible architecture admits a **pinned** mirror (first index `0`) and the
  standard admissible derivation, well-formed. -/
theorem crown_eligible_pin_structural_mirror {BD : Type u} {n : Nat}
    (A : CompressionArchitecture BD n) (h : CrownEligible A) :
    ∃ i : Fin n, ∃ d : AdmissibleSummitDerivation,
      PinnedMirrorsArchitecture A d i ∧ WellFormedAdmissible d := by
  obtain ⟨hn, _, hprof⟩ := h
  have h0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  refine ⟨⟨0, h0⟩, admissibleStandard, ?_, ic_universal_theorem_summit⟩
  refine ⟨ic_universal_theorem_summit, admissibleStandard_records_standard_shape, ?_⟩
  exact hprof ⟨0, h0⟩

/-- Alternative packaging of **T-B7.1** (`crown_eligible_induces_mirror`) from **T-P1.1** via
  `mirrorsArchitecture_of_pinned`. -/
theorem crown_eligible_induces_mirror_from_pin {BD : Type u} {n : Nat}
    (A : CompressionArchitecture BD n) (h : CrownEligible A) :
    ∃ d : AdmissibleSummitDerivation, MirrorsArchitecture A d ∧ WellFormedAdmissible d := by
  obtain ⟨_, d, hpd, hwf⟩ := crown_eligible_pin_structural_mirror A h
  exact ⟨d, ⟨mirrorsArchitecture_of_pinned hpd, hwf⟩⟩

end InfinityCompression.MetaProof
