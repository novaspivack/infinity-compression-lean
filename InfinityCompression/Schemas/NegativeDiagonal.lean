/-
  EPIC 005 — Negative diagonal schema (Theorem 5.1)

  The program spec’s `HasRepresentability.diagonal_self_opposes` as written
  (`opposes a a`) is unsatisfiable for irreflexive `opposes` (e.g. `· ≠ ·` on `Bool`).
  We formalize representability as opposition along the **anti-datum axis** at a chosen
  diagonal index — the content used in Cantor-style EPIC 008 instantiations.
-/

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.SelfPresentation

universe u1 u2 u3 u4

namespace InfinityCompression.Schemas

open Classical
open InfinityCompression.Core

class AntiContactRule {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    (F : SelfPresentedFamily I L C V) (opposes : V → V → Prop) where
  antiDatum : V → V
  opposes_anti : ∀ v : V, opposes (antiDatum v) v

/-- Diagonal index + opposition along the anti-datum axis at that index. -/
class HasRepresentability {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    (F : SelfPresentedFamily I L C V) (opposes : V → V → Prop)
    [A : AntiContactRule F opposes] where
  diagonal_index : I
  diagonal_opposes :
    opposes (A.antiDatum (F.selfContactAt diagonal_index)) (F.selfContactAt diagonal_index)

/-- From `AntiContactRule` alone, at any `i` the anti-axis opposes the datum. -/
theorem diagonal_opposes_of_anti {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    {F : SelfPresentedFamily I L C V}
    {opposes : V → V → Prop} [A : AntiContactRule F opposes] (i : I) :
    opposes (A.antiDatum (F.selfContactAt i)) (F.selfContactAt i) :=
  A.opposes_anti (F.selfContactAt i)

instance hasRepresentability_of_inhabited {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    (F : SelfPresentedFamily I L C V) (opposes : V → V → Prop)
    [Inhabited I] [AntiContactRule F opposes] : HasRepresentability F opposes where
  diagonal_index := default
  diagonal_opposes := diagonal_opposes_of_anti (default : I)

noncomputable def antiEscLoc {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    [DecidableEq C] [Inhabited I]
    (F : FaithfulSelfPresentation I L C V) (opposes : V → V → Prop)
    [A : AntiContactRule F.toSPF opposes] : Unit → C → V :=
  fun _ c =>
    @dite V (∃ i, F.toSPF.contact i = c) (Classical.propDecidable _)
      (fun h => A.antiDatum (F.toSPF.selfContactAt (Classical.choose h)))
      (fun _ => A.antiDatum (F.toSPF.selfContactAt (default : I)))

/-- From an anti-contact rule and injective `contact`, build an escape witness on `Unit`. -/
noncomputable def escapeWitnessOfAnti {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    [DecidableEq C] [Inhabited I]
    (F : FaithfulSelfPresentation I L C V) (opposes : V → V → Prop)
    [A : AntiContactRule F.toSPF opposes] : EscapeWitness (W := Unit) F.toSPF opposes where
  escape := ()
  escLoc := antiEscLoc F opposes
  opposes_all := fun i => by
    classical
    have hxi : ∃ j, F.toSPF.contact j = F.toSPF.contact i := ⟨i, rfl⟩
    have hji : Classical.choose hxi = i := F.contact_injective (Classical.choose_spec hxi)
    dsimp [antiEscLoc]
    simp only [dif_pos hxi]
    rw [hji]
    exact A.opposes_anti (F.toSPF.selfContactAt i)

/-- **Theorem 5.1** — negative diagonal schema. `HasRepresentability` is listed to match the
  program spec; it is derivable from `AntiContactRule` + `Inhabited I` (see
  `hasRepresentability_of_inhabited`). -/
theorem negative_diagonal_schema
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    [DecidableEq C] [Inhabited I]
    {F : FaithfulSelfPresentation I L C V}
    {opposes : V → V → Prop}
    [AntiContactRule F.toSPF opposes]
    [HasRepresentability F.toSPF opposes] :
    ∃ _ : EscapeWitness (W := Unit) F.toSPF opposes,
      ({ hasFiniteCharacterization := True
         hasVerificationReduction := True
         hasTransferConcentration := True
         hasRepresentationEconomy := True
         hasUniformity := False } : CompressionProfile).hasTransferConcentration :=
  ⟨escapeWitnessOfAnti F opposes, trivial⟩

end InfinityCompression.Schemas
