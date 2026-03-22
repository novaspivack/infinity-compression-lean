/-
  EPIC_004_PM3 — **Phase 2** (layer 1): **constructive derivation skeleton** from architecture-local
  data only.

  **D-P2.0** — `ConstructiveDerivationSkeleton` pins two distinct nodes with **separated polarities**
  (the object-side “dual pole” witness available from `CrownEligible` without any summit theorem).

  **T-P2.1** — `crown_eligible_constructive_skeleton` extracts such a skeleton from crown eligibility.

  **scope: semantic** — this layer uses only `CompressionArchitecture` + `CrownEligible` hypotheses.
-/

import InfinityCompression.MetaProof.CrownEligible

universe u

namespace InfinityCompression.MetaProof

open InfinityCompression.Core
open InfinityCompression.Meta

/-- **D-P2.0** — Local dual-pole witness on an architecture: two distinct indices with different
  polarities. (Under `CrownEligible`, every node has `nv32InductionProfile`; separation is polarity.) -/
structure ConstructiveDerivationSkeleton {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n) :
    Type where
  /-- First pole site. -/
  pole₀ : Fin n
  /-- Second pole site. -/
  pole₁ : Fin n
  /-- Distinctness of sites. -/
  distinct : pole₀ ≠ pole₁
  /-- Polarity contrast (not necessarily positive vs negative — any inequality of polarities). -/
  polaritySep : (A.nodes pole₀).polarity ≠ (A.nodes pole₁).polarity

/-- **T-P2.1** — Crown-eligible architectures inhabit the skeleton type (purely from object hypotheses).

  Proof is `Prop`-valued (`Nonempty`); eliminating `∃ i j, …` into a **term** of type
  `ConstructiveDerivationSkeleton` in general requires `Classical` (see tactics in
  `NonPackagingConstruction.lean` that use explicit witnesses instead). -/
theorem crown_eligible_nonempty_skeleton {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)
    (h : CrownEligible A) : Nonempty (ConstructiveDerivationSkeleton A) := by
  rcases h.2.1 with ⟨i, j, hij, hp⟩
  exact ⟨⟨i, j, hij, hp⟩⟩

end InfinityCompression.MetaProof
