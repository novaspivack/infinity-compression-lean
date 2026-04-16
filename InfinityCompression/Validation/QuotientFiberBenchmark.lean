/-
  EPIC_015_WV1 — **Program W** external benchmark: quotient fibers as the generic mathematical
  pattern behind IC’s forgetful / fiber layer (**EPIC_009** `fiberAtBare`).

  **External statement:** Every element of a quotient has a representative in the carrier
  (`Quotient.exists_rep` — standard across algebra / topology courses).

  **Architecture-guided packaging (D-WV.2):** separate **bare** data (`Quotient s`) from
  **enriched witness** data (`α`) and package the fiber as a subtype `QuotientFiber`.
  **T-WV.2.1** — `quotient_fiber_nonempty` — nonempty fiber over every bare point.

  **Wave 2 (STRONG):** From surjectivity of `forgetToQuotient`, recover **HasRightInverse**
  (`Mathlib.Logic.Function.Basic` — `surjective_iff_hasRightInverse`). Identify Mathlib’s
  canonical section **`Quotient.out`** as an actual **RightInverse** of the projection, and
  package **`canonicalQuotientFiberWitness`** — a **uniform** enriched witness over every bare
  point, not merely `Nonempty`. This is the same *mathematical* content as `Quotient.out_eq`,
  but the **corollary bundle** (section + canonical fiber point) matches the IC paper’s
  “collapse then distinguished witness upstairs” template in a way `exists_rep` alone does not
  state as a single typed interface.

  For narrative comparison of baseline Mathlib facts versus the IC fiber packaging, see the repository README
  and published papers on Program W validation.
-/

import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.Validation

variable {α : Type u} {s : Setoid α}

/-- **Bare** layer after collapsing by `s`: a point of the quotient (certificate after quotienting). -/
abbrev BareQuotient (α : Type u) (s : Setoid α) : Type u :=
  Quotient s

/-- **Enriched** carrier before collapse: elements of `α` map to bare points via `Quotient.mk`. -/
abbrev EnrichedCarrier (α : Type u) (_s : Setoid α) : Type u :=
  α

/-- Canonical projection / forgetful map from enriched carrier to bare quotient. -/
@[simp]
def forgetToQuotient (a : α) : BareQuotient α s :=
  Quotient.mk s a

/-- **D-WV.2 (specialization).** Fiber over a bare quotient point: witnesses that project to `q`. -/
def QuotientFiber (q : BareQuotient α s) : Type u :=
  { a : α // forgetToQuotient (s := s) a = q }

/-- **T-WV.2.1** — Every bare quotient point has nonempty fiber (external `Quotient.exists_rep`). -/
theorem quotient_fiber_nonempty (q : Quotient s) : Nonempty (QuotientFiber (s := s) q) := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep q
  exact ⟨⟨a, ha⟩⟩

/-- Surjectivity of `Quotient.mk` phrased in Program W vocabulary. -/
theorem forgetToQuotient_surjective : Function.Surjective (forgetToQuotient (α := α) (s := s)) :=
  fun q => Quotient.exists_rep q

/-! ### Wave 2 — section / right-inverse packaging (STRONG benchmark spine) -/

/-- **T-WV.strong.1** — Projection admits a (global) right inverse: ∃ section `β → α` after surjectivity. -/
theorem forgetToQuotient_hasRightInverse :
    Function.HasRightInverse (forgetToQuotient (α := α) (s := s)) :=
  forgetToQuotient_surjective.hasRightInverse

/-- **T-WV.strong.2** — Mathlib’s canonical `Quotient.out` is a **RightInverse** of `forgetToQuotient`. -/
theorem quotientOut_rightInverse_forgetToQuotient :
    Function.RightInverse (Quotient.out : Quotient s → α) (forgetToQuotient (α := α) (s := s)) :=
  Quotient.out_eq

/-- **T-WV.strong.3** — Uniform canonical witness in each fiber (stronger than `Nonempty` alone). -/
noncomputable def canonicalQuotientFiberWitness (q : Quotient s) : QuotientFiber (s := s) q :=
  ⟨Quotient.out q, Quotient.out_eq q⟩

/-- Alternative to **T-WV.2.1** using the canonical witness. -/
theorem quotient_fiber_nonempty' (q : Quotient s) : Nonempty (QuotientFiber (s := s) q) :=
  Nonempty.intro (canonicalQuotientFiberWitness q)

end InfinityCompression.Validation
