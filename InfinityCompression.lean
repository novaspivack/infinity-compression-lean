/-
  Infinity Compression — Lean workspace (EPIC 002 Core Definitions)
-/

import InfinityCompression.Core.SelfPresentation
import InfinityCompression.Core.FaithfulSelfPresentation
import InfinityCompression.Core.LocalWitnessSpace
import InfinityCompression.Core.InteractionStructure
import InfinityCompression.Core.LocalCoherence
import InfinityCompression.Core.GlobalRealization
import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Core.EscapeWitness
import InfinityCompression.Core.CompletionOperatorClass
import InfinityCompression.Core.EscapeOperatorClass
import InfinityCompression.Core.BurdenTypes
import InfinityCompression.Core.CompressionProfile
import InfinityCompression.Core.FailureModes
import InfinityCompression.Schemas.PositiveDiagonal
import InfinityCompression.Schemas.NegativeDiagonal
import InfinityCompression.Schemas.PolarityExclusion
import InfinityCompression.Schemas.NonVacuity
import InfinityCompression.Bridges.SRIAsEscapeWitness
import InfinityCompression.Bridges.BornRuleAsCompletion
import InfinityCompression.Bridges.GPTClosureAsCompletion
import InfinityCompression.Bridges.FoundationalAdmissibilityAsCompletion
import InfinityCompression.Bridges.AdmissibleContinuationAsCompletion
import InfinityCompression.Bridges.NoFinalSelfTheoryAsLimit
import InfinityCompression.Bridges.ReflexiveClosureAsLimit
import InfinityCompression.Bridges.CascadeAsArchitecture
import InfinityCompression.Bridges.RSUCAsArchitecture
import InfinityCompression.Meta.CompressionInstance
import InfinityCompression.Meta.CompressionChain
import InfinityCompression.Meta.CompressionArchitecture
import InfinityCompression.Meta.CompressionComposition
import InfinityCompression.Meta.CompressionCollapse
import InfinityCompression.Meta.NEMSSpineAsArchitecture
import InfinityCompression.Examples
import InfinityCompression.Frontier.PositiveDecomposition
import InfinityCompression.Frontier.ReflexiveArchitecture
import InfinityCompression.Frontier.ReflexiveArchitectureNecessity
import InfinityCompression.Frontier.ICUniversalTheorem
import InfinityCompression.Frontier.SummitDerivation
import InfinityCompression.Frontier.ICAntiTranslation
import InfinityCompression.Frontier.NoFinalPositiveCompressor
import InfinityCompression.Frontier.InternalCompressionWithoutTotalization
import InfinityCompression.Frontier.CompressionSelectivity
import InfinityCompression.Frontier.PolarityBalance
import InfinityCompression.Frontier.ProofToolValidation
import InfinityCompression.Validation.QuotientFiberBenchmark
import InfinityCompression.Validation.ProductProjectionFiberBenchmark
import InfinityCompression.Validation.SigmaFiberBenchmark
import InfinityCompression.Validation.SumCoproductFiberBenchmark
import InfinityCompression.Validation.SubtypeValFiberBenchmark
import InfinityCompression.Validation.OrbitRelationQuotientFiberBenchmark
import InfinityCompression.Validation.IdealQuotientFiberBenchmark
import InfinityCompression.MetaProof.SummitTargets
import InfinityCompression.MetaProof.DependencyShape
import InfinityCompression.MetaProof.AdmissibleDerivations
import InfinityCompression.MetaProof.RouteBFirstTheorems
import InfinityCompression.MetaProof.DerivationNecessity
import InfinityCompression.MetaProof.CrownEligible
import InfinityCompression.MetaProof.ArchitectureDerivationCorrespondence
import InfinityCompression.MetaProof.DerivationInevitability
import InfinityCompression.MetaProof.MetaCrown
import InfinityCompression.MetaProof.ProgramECrownSummit
import InfinityCompression.MetaProof.ProgramE006EReflectiveFixedPoint
import InfinityCompression.MetaProof.ReflectiveMirrorWitness
import InfinityCompression.MetaProof.AutonomousMirrorConstruction
import InfinityCompression.MetaProof.NonPackagingCorrespondence
import InfinityCompression.MetaProof.ConstructiveDerivationSkeleton
import InfinityCompression.MetaProof.LocalToGlobalDerivation
import InfinityCompression.MetaProof.NonPackagingConstruction
import InfinityCompression.MetaProof.RoleSeparatedSkeleton
import InfinityCompression.MetaProof.MetaSummitProvenance
import InfinityCompression.MetaProof.SkeletonIndexedExtractionBridge
import InfinityCompression.MetaProof.EnrichedAdmissibleSummitDerivation
import InfinityCompression.MetaProof.SkeletonDependentExtraction
import InfinityCompression.MetaProof.CanonicalCertification
import InfinityCompression.MetaProof.ReflectiveSplit
import InfinityCompression.MetaProof.EnrichedIrreducibility
import InfinityCompression.MetaProof.CanonicalCertificationNontrivialRealization
import InfinityCompression.MetaProof.ReflectiveRouteComparison
import InfinityCompression.MetaProof.ReflectiveFiberClassification
import InfinityCompression.MetaProof.GeneralizedReflectiveFiberRefinement
import InfinityCompression.MetaProof.RouteAdequacy
import InfinityCompression.MetaProof.RouteClasses
import InfinityCompression.MetaProof.RouteNecessity
import InfinityCompression.MetaProof.RouteMinimality
import InfinityCompression.MetaProof.RouteEquivalence
import InfinityCompression.MetaProof.RouteUniqueness
import InfinityCompression.MetaProof.ReflectiveCertificationArchitecture
import InfinityCompression.MetaProof.BroadClassTheorems
import InfinityCompression.MetaProof.RouteForcedContinuation

namespace InfinityCompression

/-- EPIC 002 root re-export marker. -/
def epic002Core := ()

/-- EPIC 003 — profile, burden types, failure modes. -/
def epic003Core := ()

/-- EPIC 004 — positive diagonal schema (typeclasses + Theorem 4.1). -/
def epic004Schemas := ()

/-- EPIC 005–006 — negative diagonal, polarity exclusion. -/
def epic005_006Schemas := ()

/-- EPIC 009 — non-vacuity and separation (`Schemas/NonVacuity.lean`). -/
def epic009NonVacuity := ()

/-- EPIC 010 — NEMS bridges: negative (`Bridges/SRIAsEscapeWitness.lean`; Mathlib SRI shape + nv28 barrier). -/
def epic010NemsBridgesNegative := ()

/-- EPIC 013 (initial) — compression instances / chains / complementarity. -/
def epic013Meta := ()

/-- EPIC 007–008 — canonical examples (singleton positive, Cantor-style negative, barriers). -/
def epic007_008Examples := ()

/-- Tranche 6 — EPICs 015–016 (`Frontier/PositiveDecomposition`, `Frontier/ReflexiveArchitecture`). -/
def epic015_016Frontier := ()

/-- Tranche 7 — EPICs 017–018 (`Frontier/NoFinalPositiveCompressor`, …). -/
def epic017_018UniversalLaws := ()

/-- Tranche 8 — EPIC 019 (`Frontier/ProofToolValidation`). -/
def epic019ProofToolValidation := ()

/-- EPIC_015_WV1 — Program W external proof-architecture validation (`Validation/QuotientFiberBenchmark`). Not Lean tranche EPIC 015 (`Frontier/PositiveDecomposition`). -/
def epic015wvProgramW := ()

/-- EPIC_017_EV1 — extended external validation dimensions T4–T7 (`Validation/{SumCoproduct,SubtypeVal,OrbitRelationQuotient,IdealQuotient}FiberBenchmark`). -/
def epic017evExtendedValidationDimensions := ()

/-- EPIC_001 §2.5 — IC Universal Theorem summit (`Frontier/ICUniversalTheorem.lean`). -/
def epic001UniversalSummit := ()

/-- EPIC_001 §7.5 — IC-only statement of UL-3/UL-4 (`Frontier/ICAntiTranslation.lean`). -/
def epic001AntiTranslation := ()

/-- EPIC_002_BH2 / EPIC_003_BH6 / EPIC_004_PM3 / EPIC_005_RK7 — Route B meta-layer (`MetaProof/*`: Phase 2 interface + **T-P3.1**–**T-P3.3** meta-summit provenance). -/
def epic002RouteBMeta := ()

end InfinityCompression
