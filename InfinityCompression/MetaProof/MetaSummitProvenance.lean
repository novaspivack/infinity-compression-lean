/-
  EPIC_005_RK7 — **meta-summit provenance**: pair a certified `AdmissibleSummitDerivation` with a
  **role-separated skeleton** (pole assignment on the architecture).

  **D-P3.4** — `MetaSummitWitness`: same summit-level record can carry **different** role data — the
  “meta-summit” layer is **not** reducible to the bare admissible record alone.

  **T-P3.3** — `nems_meta_summit_provenance_nontrivial`: on the NEMS spine, **one** `admissibleStandard`
  supports **two** distinct role skeletons — **provenance variance** while the derivation term is fixed.

  **scope: meta-summit / provenance** — does **not** defeat **T-P2.7** at the `AdmissibleSummitDerivation`
  equality class (same proof terms ⇒ same bare record); it **does** realize EPIC_005 §6.1 “short success”
  at the **tagged witness** level. **Full** skeleton-sensitive extraction (witness maps varying **inside**
  the admissible record) remains the open EPIC_005 target — see spec **§8.1**.
-/

import InfinityCompression.MetaProof.AdmissibleDerivations
import InfinityCompression.MetaProof.RoleSeparatedSkeleton

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Frontier
open InfinityCompression.Meta

/-- **D-P3.4** — Summit certificate + role-separated pole assignment (meta-layer packaging). -/
structure MetaSummitWitness {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) : Type where
  derivation : AdmissibleSummitDerivation
  roles : RoleSeparatedSkeleton A

/-- **T-P3.3** — Same admissible derivation, two distinct role skeletons on the NEMS spine
  (meta-summit provenance is nontrivial). -/
theorem nems_meta_summit_provenance_nontrivial :
    ∃ w₁ w₂ : MetaSummitWitness nemsSpineChain.toArchitecture,
      w₁.derivation = w₂.derivation ∧ w₁.roles ≠ w₂.roles := by
  refine ⟨⟨admissibleStandard, nemsRoleSkeleton_1_0⟩, ⟨admissibleStandard, nemsRoleSkeleton_3_2⟩, rfl, ?_⟩
  intro h
  have hr : nemsRoleSkeleton_1_0 = nemsRoleSkeleton_3_2 := by
    simpa [MetaSummitWitness] using h
  exact nems_role_skeletons_ne hr

end InfinityCompression.MetaProof
