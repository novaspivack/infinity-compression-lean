/-
  EPIC 012 — reflexive / dynamic limit bridges (T-12.2, T-12.3).
-/

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionInstance

namespace InfinityCompression.Bridges

open InfinityCompression.Core
open InfinityCompression.Meta

private def closureLimitUnit : CompressionInstance Unit :=
  { polarity := CompressionPolarity.limit
    source := ()
    target := ()
    profile := nv33ClosureProfile
    nontrivial := Or.inr trivial }

private def dynamicLimitUnit : CompressionInstance Unit :=
  { polarity := CompressionPolarity.limit
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

/-- T-12.2 — closure-without-collapse as a limit instance with verification-style profile. -/
theorem reflexive_closure_is_compression_limit :
    ∃ i : CompressionInstance Unit,
      i.polarity = CompressionPolarity.limit ∧ i.profile.hasVerificationReduction :=
  ⟨closureLimitUnit, rfl, trivial⟩

/-- T-12.3 — non-terminal completion / unfolding: limit + non-uniform profile (dynamic barrier). -/
theorem reflexive_unfolding_is_dynamic_limit :
    ∃ i : CompressionInstance Unit,
      i.polarity = CompressionPolarity.limit ∧ ¬ i.profile.hasUniformity :=
  ⟨dynamicLimitUnit, rfl, id⟩

end InfinityCompression.Bridges
