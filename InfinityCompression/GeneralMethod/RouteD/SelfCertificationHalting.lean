/-
  EPIC_GS1 Milestone 2 — Route D (logic / computability discharge).

  **Mathematical content:**

  A minimal Gödel-alignment anchor in Mathlib’s computability layer: the halting predicate
  “code `c` halts on input `n`” is **not** a computable predicate (`ComputablePred`). So any
  identification of “certification” with *computable decidability* cannot exhaust the
  realization predicate “actually halts” — a precise non-exhaustion phenomenon stated without
  IC vocabulary.

  This is not a restatement of full Gödel incompleteness for arithmetic, but it is a standard,
  formal, proof-system–level limit theorem with the same philosophical shape as Route D in
  EPIC_GS1.

  **Reference:** Mathlib `Computability.Halting` (`ComputablePred.halting_problem`).
-/

import Mathlib.Computability.Halting

namespace InfinityCompression.GeneralMethod.RouteD

open ComputablePred

/-- Route D discharge: halting-on-fixed-input is not computably decidable as a predicate on codes. -/
alias routeD_halting_notComputablePred := halting_problem

theorem routeD_certification_cannot_equal_halting_realization (n : ℕ) :
    ¬ComputablePred (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c n).Dom) :=
  halting_problem n

/-- Halting is r.e. but not computable — strict separation relevant to “certificate vs realization”. -/
alias routeD_halting_re := halting_problem_re

alias routeD_halting_complement_not_re := halting_problem_not_re

end InfinityCompression.GeneralMethod.RouteD
