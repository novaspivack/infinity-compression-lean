/-
  EPIC 006 — Polarity exclusion (Theorem 6.1)

  The program spec’s `hIncompat` quantifies `∀ v w, GRS.realizes v w → opposes v w → False`.
  At each contact `i`, completion displays `globLoc complete (contact i)` while escape
  displays `escLoc escape (contact i)`; we assume **contact alignment** between those
  displayed values. Without it, the spec’s single pair `(v,w)` cannot instantiate both
  witness families simultaneously.
-/

import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Core.SelfPresentation

universe u1 u2 u3 u4 u5 u6

namespace InfinityCompression.Schemas

open InfinityCompression.Core

/-- **Theorem 6.1** — completion and escape are incompatible once realization and opposition
  clash at aligned contact displays. -/
theorem polarity_exclusion
    {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4} {G : Type u5} {W : Type u6}
    [Inhabited I]
    {F : SelfPresentedFamily I L C V}
    {GRS : GlobalRealizationSpace G C V}
    {opposes : V → V → Prop}
    (hΓ : CompletionWitness F GRS)
    (hΔ : EscapeWitness (W := W) F opposes)
    (hAlign : ∀ i : I, GRS.globLoc hΓ.complete (F.contact i) = hΔ.escLoc hΔ.escape (F.contact i))
    (hIncompat : ∀ v w : V, GRS.realizes v w → opposes v w → False) :
    False := by
  have hr := hΓ.realizes_all (default : I)
  have ho := hΔ.opposes_all (default : I)
  rw [← hAlign] at ho
  exact hIncompat _ _ hr ho

end InfinityCompression.Schemas
