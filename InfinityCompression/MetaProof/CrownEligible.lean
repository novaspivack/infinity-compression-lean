/-
  EPIC_003_BH6 — B-006b: **CrownEligible** on compression architectures (object-side Route B).

  Structural predicate: ≥2 nodes, **polarity variation** somewhere, **uniform nv32** profile on every node.
  Not an alias to `CrownPositiveCompression` on instances (EPIC_002 §8).
-/

import Mathlib.Tactic

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionArchitecture
import InfinityCompression.Meta.NEMSSpineAsArchitecture

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Core
open InfinityCompression.Meta

/-- **D-B6b.1** — Crown-eligible architecture: large enough for polarity contrast + spine-aligned nv32
  profile on all nodes. -/
def CrownEligible {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) : Prop :=
  1 < n ∧
    (∃ i j : Fin n, i ≠ j ∧ (A.nodes i).polarity ≠ (A.nodes j).polarity) ∧
      ∀ k : Fin n, (A.nodes k).profile = nv32InductionProfile

/-- **T-B6b.1** — NEMS spine architecture is crown-eligible. -/
theorem nems_spine_architecture_crown_eligible : CrownEligible nemsSpineChain.toArchitecture := by
  refine ⟨by decide, ?_, ?_⟩
  · refine ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ?_, ?_⟩
    · decide
    · simp [nemsSpineChain, CompressionChain.toArchitecture, spineStep]
  · intro k
    fin_cases k <;> simp [nemsSpineChain, CompressionChain.toArchitecture, spineStep,
      nv32InductionProfile]

/-- **D-B6b.3** — Separation: a one-node architecture cannot be crown-eligible (fails `1 < n`). -/
theorem not_crown_eligible_architecture_one_node {BD : Type u} (A : CompressionArchitecture BD 1) :
    ¬ CrownEligible A := by
  intro h
  exact Nat.lt_irrefl 1 h.1

end InfinityCompression.MetaProof
