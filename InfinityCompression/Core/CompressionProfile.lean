/-
  EPIC 003 — Compression profile (Def 3.2) + NV-3.2/3.3 + SEP-3.3
-/

import Mathlib.Data.Nat.Bits

namespace InfinityCompression.Core

/-- Def 3.2 — gain predicates (profile), not a single scalar. -/
structure CompressionProfile where
  hasFiniteCharacterization : Prop
  hasVerificationReduction : Prop
  hasTransferConcentration : Prop
  hasRepresentationEconomy : Prop
  hasUniformity : Prop

/-- Predicate profile: induction on `ℕ` concentrates infinitely many base obligations in one schema. -/
def nv32InductionProfile : CompressionProfile :=
  { hasFiniteCharacterization := True
    hasVerificationReduction := True
    hasTransferConcentration := True
    hasRepresentationEconomy := True
    hasUniformity := False }

example : nv32InductionProfile.hasTransferConcentration := trivial

/-- Closure-operator style profile: one fixed-point check replaces pointwise verification. -/
def nv33ClosureProfile : CompressionProfile :=
  { hasFiniteCharacterization := True
    hasVerificationReduction := True
    hasTransferConcentration := False
    hasRepresentationEconomy := True
    hasUniformity := False }

example : nv33ClosureProfile.hasVerificationReduction := trivial

/-- Decode `Fin 32` into the `2^5` truth assignments for the five profile fields (bit order below). -/
def compressionProfileOfIndex (i : Fin 32) : CompressionProfile :=
  let n := i.val
  { hasFiniteCharacterization := n.testBit 0
    hasVerificationReduction := n.testBit 1
    hasTransferConcentration := n.testBit 2
    hasRepresentationEconomy := n.testBit 3
    hasUniformity := n.testBit 4 }

theorem compressionProfileOfIndex_spec (i : Fin 32) :
    (compressionProfileOfIndex i).hasFiniteCharacterization = i.val.testBit 0 ∧
      (compressionProfileOfIndex i).hasVerificationReduction = i.val.testBit 1 ∧
        (compressionProfileOfIndex i).hasTransferConcentration = i.val.testBit 2 ∧
          (compressionProfileOfIndex i).hasRepresentationEconomy = i.val.testBit 3 ∧
            (compressionProfileOfIndex i).hasUniformity = i.val.testBit 4 := by
  simp [compressionProfileOfIndex]

/-- SEP-3.3: every subset of the five flags occurs as some `CompressionProfile`. -/
theorem sep_profile_independence (i : Fin 32) :
    ∃ p : CompressionProfile,
      p.hasFiniteCharacterization = i.val.testBit 0 ∧
        p.hasVerificationReduction = i.val.testBit 1 ∧
          p.hasTransferConcentration = i.val.testBit 2 ∧
            p.hasRepresentationEconomy = i.val.testBit 3 ∧
              p.hasUniformity = i.val.testBit 4 :=
  ⟨_, compressionProfileOfIndex_spec i⟩

end InfinityCompression.Core
