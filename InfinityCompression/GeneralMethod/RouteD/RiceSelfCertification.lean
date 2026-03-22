/-
  EPIC_GS1 Route D (completion) — **Rice’s theorem** as a self-certification limit.

  No nontrivial semantic class of partial recursive functions (given extensionally by `eval`)
  is decidable as a computable predicate on codes. This is the standard “limit of
  internal certification” in computability: **membership in a nontrivial semantic class is not
  computably decidable from codes**.

  Together with `SelfCertificationHalting.lean`, this gives both a **halting** anchor and a
  **general semantic non-classifiability** anchor for Route D.

  **Reference:** Mathlib `Computability.Halting` (`ComputablePred.rice`, `ComputablePred.rice₂`).
-/

import Mathlib.Computability.Halting

namespace InfinityCompression.GeneralMethod.RouteD

open ComputablePred Nat.Partrec.Code

/-- Rice: if a class of p.r. functions is decidable on codes, it is closed under extensional
equality of `eval` (for two given p.r. functions in the class). -/
alias routeD_rice := rice

/-- Rice (set form): the only computably decidable *code* classes closed under `eval` equality
are `∅` and `univ`. -/
alias routeD_rice₂ := rice₂

/-- Post / RE–co-RE characterization of computable predicates (classical). -/
alias routeD_computable_iff_re_and_core := computable_iff_re_compl_re'

end InfinityCompression.GeneralMethod.RouteD
