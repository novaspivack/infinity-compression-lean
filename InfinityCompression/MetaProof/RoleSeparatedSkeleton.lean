/-
  EPIC_005_RK7 — **role-separated skeleton** (architecture-local polarity roles).

  **D-P3.0** — `PositiveRoleWitness` / `NegativeRoleWitness` as **local** predicates on a node index
  (positive / negative `CompressionPolarity`). No summit imports.

  **D-P3.1** — `RoleSeparatedSkeleton`: distinct **pos** and **neg** poles with matching polarity at each.

  **T-P3.1** — `nems_spine_nonempty_role_separated_skeleton`: the NEMS spine architecture carries at least
  one such skeleton (constructive witness).

  **T-P3.2** — `nems_spine_two_distinct_role_skeletons`: two **distinct** role-separated skeletons on the
  **same** architecture — **modest meta-summit provenance** (pole choice varies; `AdmissibleSummitDerivation`
  may still coincide with `admissibleStandard` by proof irrelevance — see module doc).

  **scope: semantic / provenance** — addresses EPIC_005 “short success” via **distinct skeleton tags**, not
  yet non-equal `AdmissibleSummitDerivation` values.

  **`toConstructiveSkeleton`** — maps a role-separated assignment into **`ConstructiveDerivationSkeleton`**
  for the Phase 2 bridge (`SkeletonIndexedExtractionBridge.lean`).
-/

import Mathlib.Tactic

import InfinityCompression.MetaProof.ConstructiveDerivationSkeleton
import InfinityCompression.MetaProof.CrownEligible
import InfinityCompression.Meta.NEMSSpineAsArchitecture

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Core
open InfinityCompression.Meta

variable {BD : Type u} {n : Nat}

/-- **D-P3.0a** — Local “positive pole” at index `i`. -/
def PositiveRoleWitness (A : CompressionArchitecture BD n) (i : Fin n) : Prop :=
  (A.nodes i).polarity = CompressionPolarity.positive

/-- **D-P3.0b** — Local “negative pole” at index `j`. -/
def NegativeRoleWitness (A : CompressionArchitecture BD n) (j : Fin n) : Prop :=
  (A.nodes j).polarity = CompressionPolarity.negative

/-- **D-P3.1** — Two designated poles with **positive / negative** roles (stronger than generic polarity
  separation in `ConstructiveDerivationSkeleton`). -/
structure RoleSeparatedSkeleton (A : CompressionArchitecture BD n) : Type where
  posPole : Fin n
  negPole : Fin n
  distinct : posPole ≠ negPole
  posRole : PositiveRoleWitness A posPole
  negRole : NegativeRoleWitness A negPole

/-- Every role-separated assignment induces a **Phase 2** `ConstructiveDerivationSkeleton` (same poles,
  polarity contrast from positive vs negative roles). -/
def RoleSeparatedSkeleton.toConstructiveSkeleton {A : CompressionArchitecture BD n}
    (r : RoleSeparatedSkeleton A) : ConstructiveDerivationSkeleton A where
  pole₀ := r.posPole
  pole₁ := r.negPole
  distinct := r.distinct
  polaritySep := by
    rw [r.posRole, r.negRole]
    exact CompressionPolarity.pos_ne_negative

/-! ### NEMS spine (5 nodes): explicit polarities -/

private def n0 : Fin nemsSpineChain.steps.length := ⟨0, by decide⟩
private def n1 : Fin nemsSpineChain.steps.length := ⟨1, by decide⟩
private def n2 : Fin nemsSpineChain.steps.length := ⟨2, by decide⟩
private def n3 : Fin nemsSpineChain.steps.length := ⟨3, by decide⟩

private theorem nems_node0_neg :
    (nemsSpineChain.toArchitecture.nodes n0).polarity = CompressionPolarity.negative := by
  simp [n0, nemsSpineChain, CompressionChain.toArchitecture, spineStep]

private theorem nems_node1_pos :
    (nemsSpineChain.toArchitecture.nodes n1).polarity = CompressionPolarity.positive := by
  simp [n1, nemsSpineChain, CompressionChain.toArchitecture, spineStep]

private theorem nems_node2_neg :
    (nemsSpineChain.toArchitecture.nodes n2).polarity = CompressionPolarity.negative := by
  simp [n2, nemsSpineChain, CompressionChain.toArchitecture, spineStep]

private theorem nems_node3_pos :
    (nemsSpineChain.toArchitecture.nodes n3).polarity = CompressionPolarity.positive := by
  simp [n3, nemsSpineChain, CompressionChain.toArchitecture, spineStep]

private theorem n01_ne : n0 ≠ n1 := by
  intro h
  have hval : (0 : Nat) = 1 := by simpa [n0, n1] using congrArg Fin.val h
  simp at hval

private theorem n3_ne_n2 : n3 ≠ n2 := by
  intro h
  simpa [n3, n2] using congrArg Fin.val h

/-- First canonical role-separated skeleton: positive at node 1, negative at node 0. -/
def nemsRoleSkeleton_1_0 : RoleSeparatedSkeleton nemsSpineChain.toArchitecture where
  posPole := n1
  negPole := n0
  distinct := Ne.symm n01_ne
  posRole := nems_node1_pos
  negRole := nems_node0_neg

/-- Second canonical role-separated skeleton: positive at node 3, negative at node 2. -/
def nemsRoleSkeleton_3_2 : RoleSeparatedSkeleton nemsSpineChain.toArchitecture where
  posPole := n3
  negPole := n2
  distinct := n3_ne_n2
  posRole := nems_node3_pos
  negRole := nems_node2_neg

/-- **T-P3.1** — NEMS spine architecture admits a role-separated skeleton. -/
theorem nems_spine_nonempty_role_separated_skeleton :
    Nonempty (RoleSeparatedSkeleton nemsSpineChain.toArchitecture) :=
  ⟨nemsRoleSkeleton_1_0⟩

/-- **T-P3.2** — Two distinct role-separated skeletons on the same crown-bearing spine architecture. -/
theorem nems_spine_two_distinct_role_skeletons :
    ∃ s₁ s₂ : RoleSeparatedSkeleton nemsSpineChain.toArchitecture, s₁ ≠ s₂ :=
  ⟨nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, by
    intro h
    have hp := congrArg RoleSeparatedSkeleton.posPole h
    simp [nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, n1, n3] at hp⟩

/-- **T-P3.2b** — Same as **T-P3.2**, packaged as inequality of `posPole` witnesses. -/
theorem nems_role_skeletons_distinct_pos_pole :
    nemsRoleSkeleton_1_0.posPole ≠ nemsRoleSkeleton_3_2.posPole := by
  simp [nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, n1, n3]

/-- **T-P3.2c** — Definitional inequality of the two canonical NEMS role skeletons. -/
theorem nems_role_skeletons_ne : nemsRoleSkeleton_1_0 ≠ nemsRoleSkeleton_3_2 := by
  intro h
  have hp := congrArg RoleSeparatedSkeleton.posPole h
  simp [nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, n1, n3] at hp

/-- **T-P3.2d** — Distinct role skeletons induce distinct **constructive** skeletons (`pole₀` differs). -/
theorem nems_role_constructive_skeletons_ne :
    nemsRoleSkeleton_1_0.toConstructiveSkeleton ≠ nemsRoleSkeleton_3_2.toConstructiveSkeleton := by
  intro h
  have hp := congrArg ConstructiveDerivationSkeleton.pole₀ h
  simp [nemsRoleSkeleton_1_0, nemsRoleSkeleton_3_2, n1, n3, RoleSeparatedSkeleton.toConstructiveSkeleton] at hp

/-! ### Alt-terminal spine — parallel role skeletons (for a second `concreteICCertificationLayer` host) -/

private def alt_n0 : Fin nemsSpineChain_altTerminal.steps.length := ⟨0, by decide⟩
private def alt_n1 : Fin nemsSpineChain_altTerminal.steps.length := ⟨1, by decide⟩
private def alt_n2 : Fin nemsSpineChain_altTerminal.steps.length := ⟨2, by decide⟩
private def alt_n3 : Fin nemsSpineChain_altTerminal.steps.length := ⟨3, by decide⟩

private theorem nems_alt_terminal_node0_neg :
    (nemsSpineChain_altTerminal.toArchitecture.nodes alt_n0).polarity = CompressionPolarity.negative := by
  simp [alt_n0, nemsSpineChain_altTerminal, CompressionChain.toArchitecture, spineStep]

private theorem nems_alt_terminal_node1_pos :
    (nemsSpineChain_altTerminal.toArchitecture.nodes alt_n1).polarity = CompressionPolarity.positive := by
  simp [alt_n1, nemsSpineChain_altTerminal, CompressionChain.toArchitecture, spineStep]

private theorem nems_alt_terminal_node2_neg :
    (nemsSpineChain_altTerminal.toArchitecture.nodes alt_n2).polarity = CompressionPolarity.negative := by
  simp [alt_n2, nemsSpineChain_altTerminal, CompressionChain.toArchitecture, spineStep]

private theorem nems_alt_terminal_node3_pos :
    (nemsSpineChain_altTerminal.toArchitecture.nodes alt_n3).polarity = CompressionPolarity.positive := by
  simp [alt_n3, nemsSpineChain_altTerminal, CompressionChain.toArchitecture, spineStep]

private theorem alt_n01_ne : alt_n0 ≠ alt_n1 := by
  intro h
  have hval : (0 : Nat) = 1 := by simpa [alt_n0, alt_n1] using congrArg Fin.val h
  simp at hval

private theorem alt_n3_ne_n2 : alt_n3 ≠ alt_n2 := by
  intro h
  simpa [alt_n3, alt_n2] using congrArg Fin.val h

/-- Role-separated skeleton on **`nemsSpineChain_altTerminal`**, same pole indices as `nemsRoleSkeleton_1_0`. -/
def nemsAltTerminalRoleSkeleton_1_0 : RoleSeparatedSkeleton nemsSpineChain_altTerminal.toArchitecture where
  posPole := alt_n1
  negPole := alt_n0
  distinct := Ne.symm alt_n01_ne
  posRole := nems_alt_terminal_node1_pos
  negRole := nems_alt_terminal_node0_neg

/-- Second role-separated skeleton on the alt-terminal architecture (poles 3 / 2). -/
def nemsAltTerminalRoleSkeleton_3_2 : RoleSeparatedSkeleton nemsSpineChain_altTerminal.toArchitecture where
  posPole := alt_n3
  negPole := alt_n2
  distinct := alt_n3_ne_n2
  posRole := nems_alt_terminal_node3_pos
  negRole := nems_alt_terminal_node2_neg

theorem nems_alt_terminal_role_skeletons_ne : nemsAltTerminalRoleSkeleton_1_0 ≠ nemsAltTerminalRoleSkeleton_3_2 := by
  intro h
  have hp := congrArg RoleSeparatedSkeleton.posPole h
  simp [nemsAltTerminalRoleSkeleton_1_0, nemsAltTerminalRoleSkeleton_3_2, alt_n1, alt_n3] at hp

end InfinityCompression.MetaProof
