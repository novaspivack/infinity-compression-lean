/-
  EPIC 010 — NEMS bridges: negative compression (T-10.1–T-10.3).

  This repo does not vendor `nems-lean`; instead we use **Mathlib-standard** partial-recursion
  infrastructure (`Nat.Partrec.Code`) for the SRI typing shape, and reuse the EPIC 005/008
  singleton `nv28` barrier as the **MFP-2 / diagonal escape** pattern (full NEMS paper wiring
  remains an optional upstream dependency).
-/

import Mathlib.Computability.PartrecCode

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Schemas.NegativeDiagonal

namespace InfinityCompression.Bridges

open Nat.Partrec (Code)
open InfinityCompression.Core
open InfinityCompression.Schemas

/-! ### T-10.1 — SRI as a faithful self-presentation (Paper 26 shape) -/

/--
`I = Code`, `L = Code → ℕ`, `C = Code`, `V = ℕ`.

* `contact` is **quote** realized as the identity on `Code` (codes are already quoted terms).
* `loc l c` is **run** at the *functional* layer: `l c` (the local program `l` applied to code `c`).

This is a **total** presentation layer; partial recursive *semantics* is not encoded in `loc`
beyond whatever the chosen `obj i : Code → ℕ` implements. For the witness we take `obj` constant.
-/
def sriFaithful :
    FaithfulSelfPresentation Code (Code → ℕ) Code ℕ where
  obj := fun _ => fun _ => 0
  contact := id
  loc := fun l c => l c
  contact_injective := Function.injective_id
  loc_contact_separates := fun i j hij => by
    classical
    refine ⟨fun c => if c = i then 0 else 1, ?_⟩
    intro h_eq
    have hi : (fun c => if c = i then 0 else 1) i = 0 := by simp
    have hj : (fun c => if c = i then 0 else 1) j = 1 := by
      simp [Ne.symm hij]
    have hlr : (fun c => if c = i then 0 else 1) i = (fun c => if c = i then 0 else 1) j := by
      simpa [id_eq] using h_eq
    rw [hi, hj] at hlr
    simp at hlr

/-- T-10.1: the SRI typing constraints are inhabited and satisfy faithfulness/injectivity. -/
theorem sri_is_faithful_spf :
    ∃ (F : FaithfulSelfPresentation Code (Code → ℕ) Code ℕ),
      Function.Injective F.contact ∧
        (∀ l c, F.loc l c = l c) ∧
          (∀ i, F.contact i = i) :=
  ⟨sriFaithful, Function.injective_id, fun _ _ => rfl, fun _ => rfl⟩

/-! ### T-10.2 — MFP-2 / diagonal as `EscapeWitness` (singleton Bool model) -/

instance sri_bool_neq_anti : AntiContactRule nv28Family.toSPF (· ≠ ·) where
  antiDatum := not
  opposes_anti := fun v => by cases v <;> decide

/-- T-10.2: an inhabited `EscapeWitness` for inequality opposition (MFP-2 / diagonal barrier pattern). -/
theorem mfp2_is_escape_witness :
    Nonempty (EscapeWitness (W := Unit) nv28Family.toSPF (· ≠ ·)) :=
  ⟨nv28Escape⟩

/-! ### T-10.3 — Selector-strength barrier as negative compression (profile concentration) -/

/-- T-10.3: negative diagonal packaging yields `hasTransferConcentration` on the induction-style profile. -/
theorem selector_strength_barrier_is_negative_compression :
    ∃ _ : EscapeWitness (W := Unit) nv28Family.toSPF (· ≠ ·), nv32InductionProfile.hasTransferConcentration :=
  negative_diagonal_schema (F := nv28Family) (opposes := (· ≠ ·))

end InfinityCompression.Bridges
