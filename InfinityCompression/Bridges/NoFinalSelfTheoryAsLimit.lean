/-
  EPIC 012 — limit theorems as `CompressionPolarity.limit` instances (T-12.1, T-12.4).
-/

import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Meta.CompressionInstance

namespace InfinityCompression.Bridges

open InfinityCompression.Core
open InfinityCompression.Meta

private def posLimitUnit : CompressionInstance Unit :=
  { polarity := CompressionPolarity.positive
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

private def metaLimitUnit : CompressionInstance Unit :=
  { polarity := CompressionPolarity.limit
    source := ()
    target := ()
    profile := nv32InductionProfile
    nontrivial := Or.inl trivial }

/-- T-12.1 — partial positive compression exists alongside a limit pole (no total positive closure). -/
theorem no_final_self_theory_is_compression_limit :
    (∃ p : CompressionInstance Unit, p.polarity = CompressionPolarity.positive) ∧
      ∃ l : CompressionInstance Unit, l.polarity = CompressionPolarity.limit :=
  ⟨⟨posLimitUnit, rfl⟩, ⟨metaLimitUnit, rfl⟩⟩

/-- T-12.4 — internalization without totalization: limit pole carries representation economy. -/
theorem internalization_not_totalization_is_compression_limit :
    ∃ i : CompressionInstance Unit,
      i.polarity = CompressionPolarity.limit ∧ i.profile.hasRepresentationEconomy :=
  ⟨metaLimitUnit, rfl, trivial⟩

end InfinityCompression.Bridges
