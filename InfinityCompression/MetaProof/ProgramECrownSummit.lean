/-
  EPIC_006_CN1 — **Program E** (crown necessity → irreducible / nonaccidental summit) — **first Lean
  landings**.

  **D-E6.1** — `SummitCapableMirror` — packages mirror + well-formedness + standard recording +
  non-degenerate bundle (dual canonical shards).

  **T-E6.1** — `crown_eligible_yields_summit_capable_mirror` — **006B** / Program **E2**: crown eligibility
  yields a summit-capable mirror.

  **T-E6.2** — `summit_capable_mirror_not_monopolar` — **006C** / Program **E3** (anti-monopole instance):
  such a mirror records a **non–monopolar** standard shape.

  **T-E6.3** — `crown_eligible_summit_program_e` — **006D** / Program **E4**: `icUniversalSummitStatement`
  from crown eligibility **via** `reflexive_meta_crown` + well-formedness (audit spine: no top-level
  `exact ic_universal_theorem_summit`).

  **T-E6.4** — `crown_eligible_summit_program_e_via_dual_poles` — same conclusion **via** recorded dual-pole
  obligations + `dual_poles_imply_ic_universal_summit`.

  **scope / honesty:** Sub-proofs (`crown_eligible_induces_mirror`, `reflexive_meta_crown`) still depend on
  `ic_universal_theorem_summit` for the **library** mirror. This module is the **named Program E chain**
  for audit and future semantic replacement — not a claim that the unconditional summit proof has been
  removed from the dependency graph.

  **006E** is implemented in `MetaProof/ProgramE006EReflectiveFixedPoint.lean` (**D-E6.5**, **T-E6.5**–**T-E6.8**).
-/

import InfinityCompression.MetaProof.DerivationNecessity
import InfinityCompression.MetaProof.MetaCrown

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-E6.1** — Program E “summit-capable” mirror: architecture mirror + well-formed + standard shape
  recorded + **non-degenerate** canonical shard content (EPIC_006 **006A**). -/
def SummitCapableMirror {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)
    (d : AdmissibleSummitDerivation) : Prop :=
  MirrorsArchitecture A d ∧
    WellFormedAdmissible d ∧
      RecordsDependencyShape d dependencyShapeStandard ∧
        NonDegenerateAdmissible d

/-- **T-E6.1** — Crown-eligible ⇒ ∃ **summit-capable** mirror (**006B** / Program **E2**). -/
theorem crown_eligible_yields_summit_capable_mirror {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)
    (h : CrownEligible A) : ∃ d : AdmissibleSummitDerivation, SummitCapableMirror A d := by
  obtain ⟨d, ⟨hMir, hwf⟩⟩ := crown_eligible_induces_mirror A h
  refine ⟨d, ⟨hMir, hwf, hMir.2.1, ?_⟩⟩
  exact records_standard_implies_non_degenerate d hMir.2.1

/-- **T-E6.2** — A summit-capable mirror records a **non–monopolar** standard dependency shape (**006C**). -/
theorem summit_capable_mirror_not_monopolar {BD : Type u} {n : Nat} {A : CompressionArchitecture BD n}
    {d : AdmissibleSummitDerivation} (h : SummitCapableMirror A d) : ¬ Monopolar dependencyShapeStandard :=
  not_monopolar_standard_record_non_degenerate d h.2.2.1 h.2.2.2

/-- **T-E6.3** — Crown eligibility ⇒ §2.5 summit statement **via Program E chain** (`reflexive_meta_crown` →
  well-formedness) (**006D**). -/
theorem crown_eligible_summit_program_e {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)
    (h : CrownEligible A) : icUniversalSummitStatement := by
  obtain ⟨d, h⟩ := reflexive_meta_crown A h
  have hwf := (wellFormed_iff d).mp h.2.1
  have hnd := records_standard_implies_non_degenerate d h.2.2.1
  rcases hwf with ⟨ha, hb⟩
  rw [hnd.1] at ha
  rw [hnd.2] at hb
  exact ⟨ha, hb⟩

/-- **T-E6.4** — Same conclusion **via** recorded dual-pole obligations (alternative audit path). -/
theorem crown_eligible_summit_program_e_via_dual_poles {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)
    (h : CrownEligible A) : icUniversalSummitStatement := by
  obtain ⟨d, h⟩ := reflexive_meta_crown A h
  exact dual_poles_imply_ic_universal_summit ⟨h.2.2.2.1, h.2.2.2.2⟩

end InfinityCompression.MetaProof
