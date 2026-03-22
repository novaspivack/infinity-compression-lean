/-
  EPIC_018 — External validation **tranche T12**: non-surjective collapse (MODERATE control).

  **Mathematical story:** `Nat.succ` is **not** surjective (`0` is not a successor). Fibers of the
  “forgetful” reading `succFiber n = { m // succ m = n}` are nonempty **iff** `n ≠ 0`.

  **Verdict packaging:** explicit `¬ Surjective succ`, no global `HasRightInverse`; positivity
  uses a **partial** inverse (`Nat.pred`) with `succ (pred n) = n` for `n ≠ 0`.

  Imports: `Init` only (no Mathlib required).
-/

import Init.Prelude

namespace InfinityCompression.Validation

def succFiber (n : Nat) : Type :=
  { m : Nat // m.succ = n }

theorem succFiber_nonempty_iff (n : Nat) : Nonempty (succFiber n) ↔ n ≠ 0 := by
  constructor
  · intro h
    rcases h with ⟨⟨m, hm⟩⟩
    cases n with
    | zero => cases hm
    | succ _ => simp
  · intro hn
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ m => exact ⟨⟨m, rfl⟩⟩

theorem nat_succ_not_surjective : ¬Function.Surjective Nat.succ := by
  intro h
  obtain ⟨m, hm⟩ := h 0
  cases hm

theorem nat_succ_not_hasRightInverse : ¬Function.HasRightInverse Nat.succ := fun h =>
  nat_succ_not_surjective (Function.HasRightInverse.surjective h)

theorem succ_pred_eq_of_ne_zero {n : Nat} (hn : n ≠ 0) : (Nat.pred n).succ = n := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ _ => rfl

/-- `Nat.pred` is a left inverse of `Nat.succ` (global on `Nat`). -/
theorem pred_leftInverse_succ : Function.LeftInverse Nat.pred Nat.succ :=
  Nat.pred_succ

end InfinityCompression.Validation
