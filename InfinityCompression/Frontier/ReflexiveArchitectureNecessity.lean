/-
  Level-4 crown — **Summit layer S1** (structural necessity on the canonical spine).

  This is **not** a claim that “every reflexive architecture” collapses to the NEMS spine, nor that
  the IC summit **follows** from spine equality (that would require new mathematics linking
  `CompletionWitness` theory to `CompressionArchitecture` nodes). What *is* proved is:

  * the **canonical** `nemsSpineChain.toArchitecture` is **uniquely** determined by `IsCanonicalNemsSpine`;
  * on that architecture, **polarity alternation** and **uniform nv32 profile** are **forced** by
    the spine construction (not accidental).

  For the summit-as-corollary-of-one-architecture story (S2), see `SummitDerivation.lean`.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionArchitecture
import InfinityCompression.Meta.CompressionInstance
import InfinityCompression.Meta.NEMSSpineAsArchitecture

universe u

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Meta

/-- Crown eligibility predicate (v1): equality with the **canonical** five-step NEMS spine
  architecture on `Unit`. This is the strongest *definitional* “crown carrier” in the current
  library without quantifying over all DAGs. -/
def IsCanonicalNemsSpine (A : CompressionArchitecture Unit 5) : Prop :=
  A = nemsSpineChain.toArchitecture

/-- Polarity alternation along the spine nodes (matches `spineStep` construction). -/
def NemsSpinePolarityAlternates (A : CompressionArchitecture Unit 5) : Prop :=
  (A.nodes 0).polarity = CompressionPolarity.negative ∧
    (A.nodes 1).polarity = CompressionPolarity.positive ∧
      (A.nodes 2).polarity = CompressionPolarity.negative ∧
        (A.nodes 3).polarity = CompressionPolarity.positive ∧
          (A.nodes 4).polarity = CompressionPolarity.negative

/-- Every step uses the induction / spine profile (`nv32InductionProfile`). -/
def SpineUsesNv32Everywhere (A : CompressionArchitecture Unit 5) : Prop :=
  ∀ i : Fin 5, (A.nodes i).profile = nv32InductionProfile

private lemma nems_spine_polarityAlternates_aux : NemsSpinePolarityAlternates nemsSpineChain.toArchitecture := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [nemsSpineChain, CompressionChain.toArchitecture, spineStep]

private lemma nems_spine_nv32_aux : SpineUsesNv32Everywhere nemsSpineChain.toArchitecture := by
  intro i
  fin_cases i <;> simp [nemsSpineChain, CompressionChain.toArchitecture, spineStep,
    nv32InductionProfile]

private lemma nems_spine_terminal_aux :
    nemsSpineChain.toArchitecture.terminal = ⟨4, by decide⟩ := by
  simp [CompressionChain.toArchitecture, nemsSpineChain]

/-- **Summit layer S1 — structural necessity** on the canonical spine: any architecture equal to the
  spine inherits its forced polarity pattern, uniform profile, and terminal node. -/
theorem reflexive_architecture_necessity (A : CompressionArchitecture Unit 5)
    (h : IsCanonicalNemsSpine A) :
    NemsSpinePolarityAlternates A ∧ SpineUsesNv32Everywhere A ∧ A.terminal = ⟨4, by decide⟩ := by
  subst h
  exact ⟨nems_spine_polarityAlternates_aux, nems_spine_nv32_aux, nems_spine_terminal_aux⟩

/-- Uniqueness: at most one architecture satisfies `IsCanonicalNemsSpine`. -/
theorem isCanonicalNemsSpine_unique (A B : CompressionArchitecture Unit 5)
    (hA : IsCanonicalNemsSpine A) (hB : IsCanonicalNemsSpine B) : A = B := by
  simp [IsCanonicalNemsSpine] at hA hB
  exact hA.trans hB.symm

/-- The canonical spine satisfies the crown structural bundle without extra hypotheses. -/
theorem nems_spine_satisfies_crown_structure :
    NemsSpinePolarityAlternates nemsSpineChain.toArchitecture ∧
      SpineUsesNv32Everywhere nemsSpineChain.toArchitecture ∧
        nemsSpineChain.toArchitecture.terminal = ⟨4, by decide⟩ :=
  reflexive_architecture_necessity _ rfl

end InfinityCompression.Frontier
