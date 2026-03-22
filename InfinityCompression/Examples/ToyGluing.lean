/-
  EPIC 007 — T-7.4 toy gluing (degenerate cover).

  A one-element index set has a single patch; “glueing” is trivial and yields the same
  `CompletionWitness` spine as `SingletonPositive`.
-/

import InfinityCompression.Examples.SingletonPositive

namespace InfinityCompression.Examples

/-- T-7.4 (reference): singleton cover ⇒ global section = the singleton completion story. -/
abbrev toy_gluing_is_completion :=
  singleton_positive_diagonal

end InfinityCompression.Examples
