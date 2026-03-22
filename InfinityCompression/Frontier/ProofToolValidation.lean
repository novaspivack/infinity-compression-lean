/-
  EPIC 019 — Proof tool validation: two IC-abstracted results; zero `sorry` in proof terms.

  **Direct proof (baseline):** build the same-polarity chain witness by hand from list
  operations and check endpoints / TC manually.

  **IC proof (here):** reuse `collapse_for_same_polarity_positive_chain` from EPIC 013 so the
  collapse witness is obtained uniformly from `CompressionChain.aggregateProfile` and the
  positive-step closure theorem — the “proof object” is the structured chain + one theorem.

  **Second validation:** Theorem 6.2 complementarity (`polarity_complementarity`) — building a
  two-step `CompressionChain` from opposite-polarity compatible instances without hand-list
  reasoning beyond compatibility.
-/

import InfinityCompression.Meta.CompressionCollapse
import InfinityCompression.Meta.CompressionInstance
import InfinityCompression.Meta.NEMSSpineAsArchitecture

namespace InfinityCompression.Frontier

open InfinityCompression.Core
open InfinityCompression.Meta

/-- EPIC 019 target: same-polarity chain collapse packaged via `CompressionChain` (EPIC 013). -/
theorem proof_tool_validation_same_polarity_collapse (BD : Type) (ch : CompressionChain BD)
    (hpos : ∀ s ∈ ch.steps, s.polarity = CompressionPolarity.positive) :
    ∃ single : CompressionInstance BD,
      single.source = (List.head ch.steps ch.nonempty).source ∧
        single.target = (List.getLast ch.steps ch.nonempty).target ∧
          (single.profile.hasTransferConcentration ↔ ch.aggregateProfile.hasTransferConcentration) :=
  collapse_for_same_polarity_positive_chain ch hpos

/-- EPIC 019 — Theorem 6.2: compatible negative then positive steps form a two-step chain. -/
theorem proof_tool_validation_polarity_complementarity {BD : Type} (negStep posStep : CompressionInstance BD)
    (hneg : negStep.polarity = CompressionPolarity.negative)
    (hpos : posStep.polarity = CompressionPolarity.positive)
    (hComp : negStep.target = posStep.source) :
    ∃ ch : CompressionChain BD, ch.steps = [negStep, posStep] := by
  rcases polarity_complementarity negStep posStep hneg hpos hComp with ⟨ch, h⟩
  exact ⟨ch, h⟩

end InfinityCompression.Frontier
