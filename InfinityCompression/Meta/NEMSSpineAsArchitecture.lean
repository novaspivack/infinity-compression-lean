/-
  EPIC 014 — T-14.1: five-stage NEMS spine as a linear `CompressionArchitecture` (alternating polarity).
-/

import Mathlib.Tactic

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionComposition

namespace InfinityCompression.Meta

open InfinityCompression.Core

/-- One spine step at fixed polarity (shared by EPIC 014 and crown necessity proofs). -/
def spineStep (p : CompressionPolarity) : CompressionInstance Unit :=
  { polarity := p
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

/-- Five alternating steps: − + − + − on `Unit` (compatible endpoints). -/
def nemsSpineChain : CompressionChain Unit :=
  let steps := [
    spineStep CompressionPolarity.negative,
    spineStep CompressionPolarity.positive,
    spineStep CompressionPolarity.negative,
    spineStep CompressionPolarity.positive,
    spineStep CompressionPolarity.negative,
  ]
  { steps := steps
    nonempty := List.cons_ne_nil _ _
    compatible := fun i => by
      fin_cases i <;> simp }

/-- Same spine length and intermediate pattern as `nemsSpineChain`, but the **terminal** step is **positive**
(… − + − + **`+`**), yielding a **provably different** `CompressionArchitecture` (last-node polarity). Used as a
second native `CompressionArchitecture Unit` witness alongside the canonical NEMS theorem spine. -/
def nemsSpineChain_altTerminal : CompressionChain Unit :=
  let steps := [
    spineStep CompressionPolarity.negative,
    spineStep CompressionPolarity.positive,
    spineStep CompressionPolarity.negative,
    spineStep CompressionPolarity.positive,
    spineStep CompressionPolarity.positive,
  ]
  { steps := steps
    nonempty := List.cons_ne_nil _ _
    compatible := fun i => by
      fin_cases i <;> simp }

/-- The alternating-spine and alt-terminal architectures differ (terminal node polarity). -/
theorem nems_spine_architecture_ne_altTerminal :
    nemsSpineChain.toArchitecture ≠ nemsSpineChain_altTerminal.toArchitecture := by
  intro h
  let i : Fin nemsSpineChain.steps.length := ⟨4, by decide⟩
  replace h :=
    congrArg (fun A : CompressionArchitecture Unit _ => (A.nodes i).polarity) h
  simp [nemsSpineChain, nemsSpineChain_altTerminal, CompressionChain.toArchitecture, spineStep, i] at h

/-- T-14.1 — NEMS theorem spine embeds as the canonical linear architecture of `nemsSpineChain`. -/
theorem nems_spine_is_architecture :
    ∃ A : CompressionArchitecture Unit nemsSpineChain.steps.length, A = nemsSpineChain.toArchitecture :=
  ⟨nemsSpineChain.toArchitecture, rfl⟩

end InfinityCompression.Meta
