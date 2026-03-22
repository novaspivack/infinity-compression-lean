/-
  EPIC 008 — Cantor-style negative compression on `Bool` (T-8.1 reference).

  Full “no surjection α → (α → Bool)” is in Mathlib’s cardinal / function theory; here we
  package the **same combinatorial pattern** as EPIC 005: Boolean negation as anti-contact
  on the singleton `nv28` family.
-/

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.FailureModes
import InfinityCompression.Schemas.NegativeDiagonal

namespace InfinityCompression.Examples

open InfinityCompression.Core
open InfinityCompression.Schemas

instance bool_neq_anti : AntiContactRule nv28Family.toSPF (· ≠ ·) where
  antiDatum := not
  opposes_anti := fun v => by cases v <;> decide

/-- T-8.1: `EscapeWitness` from negation at the self-contact locus (diagonal-style). -/
theorem cantor_is_escape :
    ∃ _ : EscapeWitness (W := Unit) nv28Family.toSPF (· ≠ ·),
      nv32InductionProfile.hasTransferConcentration :=
  negative_diagonal_schema (F := nv28Family) (opposes := (· ≠ ·))

/-- T-8.2 (semantic barrier): halting / computability obstruction (not an `EscapeWitness`). -/
theorem halting_is_escape :
    ∃ p : Nat.Partrec.Code → Prop, ¬ ComputablePred p :=
  witness_incompleteness_barrier

end InfinityCompression.Examples
