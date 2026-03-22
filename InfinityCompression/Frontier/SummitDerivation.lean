/-
  Summit layers **S2** (derivation / packaging status) and links to **S1** (`ReflexiveArchitectureNecessity`).

  **Honest epistemology:** `icUniversalSummitStatement` is proved from completion/operator theory
  (`ICUniversalTheorem`) and does **not** currently follow from `IsCanonicalNemsSpine` by logical
  implication with a nontrivial proof term. The theorems below record (1) **joint truth** of the
  summit and spine necessity, and (2) the **biconditional** decomposition of the summit (S3 layer
  lives in `ICUniversalTheorem.ic_universal_theorem_summit_iff_components`).

  A future **true** `necessity → summit` theorem would require new machinery identifying global
  completion obstructions with properties of a chosen `CompressionArchitecture` — not merely
  equality to the NEMS spine.
-/

import InfinityCompression.Meta.CompressionArchitecture

import InfinityCompression.Frontier.ICUniversalTheorem
import InfinityCompression.Frontier.ReflexiveArchitectureNecessity

namespace InfinityCompression.Frontier

open InfinityCompression.Meta

/-- Joint availability: §2.5 summit holds **and** the canonical spine satisfies forced polarity. -/
theorem summit_and_spine_necessity_joint :
    icUniversalSummitStatement ∧
      NemsSpinePolarityAlternates nemsSpineChain.toArchitecture :=
  ⟨ic_universal_theorem_summit, nems_spine_satisfies_crown_structure.1⟩

/-- There exists a crown-eligible architecture with alternating polarity (witness = spine). -/
theorem exists_crown_eligible_with_forced_polarity :
    ∃ A : CompressionArchitecture Unit 5,
      IsCanonicalNemsSpine A ∧ NemsSpinePolarityAlternates A :=
  ⟨nemsSpineChain.toArchitecture, rfl, nems_spine_satisfies_crown_structure.1⟩

/-- **S2 (material implication).** `IsCanonicalNemsSpine A → icUniversalSummitStatement` holds
  because the conclusion is unconditionally true (`ic_universal_theorem_summit`). This is **not**
  yet a causal derivation from spine structure to completion theory; it records the implication for
  interface compatibility until a nontrivial bridge exists. -/
theorem crown_eligible_implies_summit_statement (A : CompressionArchitecture Unit 5)
    (_ : IsCanonicalNemsSpine A) : icUniversalSummitStatement :=
  ic_universal_theorem_summit

end InfinityCompression.Frontier
