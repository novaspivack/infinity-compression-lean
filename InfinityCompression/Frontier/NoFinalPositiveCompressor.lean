/-
  EPIC 017 — UL-3: no final positive compressor (DiagonalCapable + representability).

  `DiagonalCapable` is the operational bundle used here: globally inadmissible `GRS`
  (so no `CompletionWitness` exists) together with a standard halting barrier
  (`∃ p, ¬ ComputablePred p`), matching NV-17.1.
-/

import Mathlib.Computability.Halting

import InfinityCompression.Core.CompletionOperatorClass
import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.FailureModes
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Schemas.NegativeDiagonal
import InfinityCompression.Schemas.NonVacuity

universe u1 u2 u3 u4 u5

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Schemas

theorem completion_witness_excludes_inadmissible {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    {G : Type u5} (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V)
    (h : ∀ g : G, ¬ GRS.admissible g) (w : CompletionWitness F GRS) : False :=
  (h w.complete) w.admissible_complete

/-- Admissible completability: some completion witness exists for `F` in `GRS`. -/
def IsAdmissiblyCompletable {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) : Prop :=
  Nonempty (CompletionWitness F GRS)

/-- Program-spec phrasing (EPIC 017 §T-17.1): on admissible families, completion realizes all contacts.

  For `op : CompletionOperatorClass`, each `op.complete Fprm` is already a `CompletionWitness`, hence
  already satisfies `realizes_all` (Def 2.7). So this predicate is **automatically** true for every
  such `op`; the existential `∃ op, …` is therefore equivalent to `Nonempty (CompletionOperatorClass …)`.
  The diagonal obstruction is **nonexistence** of that class. -/
def completesEveryAdmissibleFamily {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (GRS : GlobalRealizationSpace G C V)
    (op : CompletionOperatorClass (FaithfulSelfPresentation I L C V) (fun F => F.toSPF) GRS) : Prop :=
  ∀ Fprm : FaithfulSelfPresentation I L C V,
    (IsAdmissiblyCompletable Fprm.toSPF GRS) →
      (∀ i : I,
        GRS.realizes (GRS.globLoc (op.complete Fprm).complete (Fprm.toSPF.contact i))
          (Fprm.toSPF.selfContactAt i))

lemma completesEveryAdmissibleFamily_of {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    {GRS : GlobalRealizationSpace G C V}
    (op : CompletionOperatorClass (FaithfulSelfPresentation I L C V) (fun F => F.toSPF) GRS) :
    completesEveryAdmissibleFamily GRS op := fun _ _ => (op.complete _).realizes_all

lemma exists_op_completesEveryAdmissibleFamily_iff {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    {G : Type u5} {GRS : GlobalRealizationSpace G C V} :
    (∃ op : CompletionOperatorClass (FaithfulSelfPresentation I L C V) (fun F => F.toSPF) GRS,
        completesEveryAdmissibleFamily GRS op) ↔
      ∃ _ : CompletionOperatorClass (FaithfulSelfPresentation I L C V) (fun F => F.toSPF) GRS, True := by
  constructor
  · rintro ⟨op, _⟩; exact ⟨op, trivial⟩
  · rintro ⟨op, _⟩; exact ⟨op, completesEveryAdmissibleFamily_of op⟩

/-- Diagonal capability for UL-3/4: inadmissible globals + halting barrier (NV-17.1). -/
def DiagonalCapable {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    (_F : SelfPresentedFamily I L C V) (GRS : GlobalRealizationSpace G C V) : Prop :=
  (∀ g : G, ¬ GRS.admissible g) ∧ (∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p)

/-- NV-17.1 — halting / inadmissible instance. -/
theorem diagonalCapable_nv28_allInadmissible :
    DiagonalCapable nv28Family.toSPF allInadmissibleGRS :=
  And.intro (fun _ hg => nomatch hg) witness_incompleteness_barrier

/-- T-17.1 — no total internal completion operator on `FaithfulSelfPresentation` (UL-3).

  Statement uses `completesEveryAdmissibleFamily` (EPIC §T-17.1’s `∀ F', … → realizes_all` bundle);
  for `CompletionOperatorClass` this is equivalent to `Nonempty` of the class
  (`exists_op_completesEveryAdmissibleFamily_iff`). Under `DiagonalCapable`, no `CompletionWitness`
  exists, so no `CompletionOperatorClass`. -/
theorem no_final_positive_compressor
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    {opposes : V → V → Prop}
    (F : FaithfulSelfPresentation I L C V)
    (GRS : GlobalRealizationSpace G C V)
    [AntiContactRule F.toSPF opposes]
    [HasRepresentability F.toSPF opposes]
    (hD : DiagonalCapable F.toSPF GRS) :
    ¬ ∃ op : CompletionOperatorClass (FaithfulSelfPresentation I L C V) (fun F => F.toSPF) GRS,
        completesEveryAdmissibleFamily GRS op := by
  classical
  intro ⟨op, _⟩
  have w := op.complete F
  exact completion_witness_excludes_inadmissible F.toSPF GRS hD.1 w

/-- Corollary: no `CompletionOperatorClass` at all (spec’s `∃ op, True` / nonempty form). -/
theorem no_final_positive_compressor_nonempty
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5}
    {opposes : V → V → Prop}
    (F : FaithfulSelfPresentation I L C V)
    (GRS : GlobalRealizationSpace G C V)
    [AntiContactRule F.toSPF opposes]
    [HasRepresentability F.toSPF opposes]
    (hD : DiagonalCapable F.toSPF GRS) :
    ¬ ∃ _ : CompletionOperatorClass (FaithfulSelfPresentation I L C V)
          (fun F => F.toSPF) GRS, True := by
  rw [← (not_iff_not.mpr exists_op_completesEveryAdmissibleFamily_iff)]
  exact @no_final_positive_compressor I L C V G opposes F GRS _ _ hD

/-- NV-17.2 — singleton closure family is admissibly completable (`nv27GRS`). -/
theorem isAdmissiblyCompletable_nv27 : IsAdmissiblyCompletable nv27Family nv27GRS :=
  Nonempty.intro nv27Completion

/-- SEP-17.1 — `DiagonalCapable` is not automatic: total completion exists on `SingletonFam`
  while `DiagonalCapable` fails for `nv27GRS`. -/
theorem sep_17_1 :
    ∃ (F : FaithfulSelfPresentation (Fin 1) (Fin 1) (Fin 1) Bool)
      (GRS : GlobalRealizationSpace Bool (Fin 1) Bool),
      ¬ DiagonalCapable F.toSPF GRS ∧
        Nonempty (CompletionOperatorClass SingletonFam singletonToSPF GRS) :=
  ⟨nv28Family, nv27GRS,
    And.intro (fun (h : DiagonalCapable nv28Family.toSPF nv27GRS) => h.1 true trivial)
      (Nonempty.intro nv29Op)⟩

end InfinityCompression.Frontier
