/-
  EPIC 007 — T-7.1 inductive / generative reading (reference hook).

  Inductive definitions “least closed under rules” share the same **singleton** completion
  spine as `SingletonPositive` at this stage of the formalization.
-/

import InfinityCompression.Examples.SingletonPositive

namespace InfinityCompression.Examples

/-- T-7.1 (reference): positive diagonal at the singleton family. -/
abbrev induction_is_completion :=
  singleton_positive_diagonal

end InfinityCompression.Examples
