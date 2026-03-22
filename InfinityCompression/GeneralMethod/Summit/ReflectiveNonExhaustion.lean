/-
  EPIC_GS1 Milestones 4 & 6 — Abstract non-exhaustion from `ReflectiveCertificationArchitecture`,
  and summit anchor packaging.

  **Milestone 4:** The broad class `ReflectiveCertificationArchitecture` (EPIC_013_BS1, IC-free
  vocabulary) already encodes “canonical certificate + proper extension of realizations”.

  **Milestone 6:** From any RCA, we derive existential **non-exhaustion** above a certificate:
  two distinct realizations share the same bare certificate. Equivalently, the forgetful map is
  not injective — the formal core of the Reflective Non-Exhaustion Theorem at the level of
  abstract certification architectures.

  **Depends on:** `MetaProof/ReflectiveCertificationArchitecture`, `ReflectiveRouteComparison`
  (`ProperExtensionViaForgetful`).
-/

import InfinityCompression.MetaProof.ReflectiveCertificationArchitecture

namespace InfinityCompression.GeneralMethod.Summit

open InfinityCompression.MetaProof

/-! ### Milestone 4 — inevitability from the RCA axioms -/

theorem rca_forget_not_injective (A : ReflectiveCertificationArchitecture) :
    ¬Function.Injective A.forget := by
  intro hf
  obtain ⟨x₁, x₂, hne, heq⟩ := A.forget_proper
  exact hne (hf heq)

/-! ### Milestone 6 — existential non-exhaustion (summit anchor) -/

theorem reflective_non_exhaustion_existential (A : ReflectiveCertificationArchitecture) :
    ∃ c : A.Cert, ∃ r₁ r₂ : A.Real, A.forget r₁ = c ∧ A.forget r₂ = c ∧ r₁ ≠ r₂ := by
  obtain ⟨r₁, r₂, hne, heq⟩ := A.forget_proper
  refine ⟨A.forget r₁, r₁, r₂, rfl, ?_, hne⟩
  exact heq.symm

/-- Two distinct realizations lie in the same certificate fiber. -/
theorem reflective_non_exhaustion_nontrivial_fiber (A : ReflectiveCertificationArchitecture) :
    ∃ c : A.Cert, ∃ r₁ r₂ : A.Real,
      r₁ ≠ r₂ ∧ r₁ ∈ A.forget ⁻¹' {c} ∧ r₂ ∈ A.forget ⁻¹' {c} := by
  obtain ⟨c, r₁, r₂, h₁, h₂, hne⟩ := reflective_non_exhaustion_existential A
  refine ⟨c, r₁, r₂, hne, ?_, ?_⟩
  · simp [Set.mem_preimage, Set.mem_singleton_iff, h₁]
  · simp [Set.mem_preimage, Set.mem_singleton_iff, h₂]

alias milestone6_reflective_non_exhaustion := reflective_non_exhaustion_existential

end InfinityCompression.GeneralMethod.Summit
