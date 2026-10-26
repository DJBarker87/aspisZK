import Lean
import WideExactInitialParityCBridgeV9
import WideExactNaturalBasisTriangularV4
import WideExactNaturalBasisTriangularV6
import WideExactNaturalBasisTriangularV8
import WideExactNaturalBasisTriangularV9
import WideExactNaturalBasisTriangularV12
import WideExactNaturalBasisTriangularV14
import WideExactInitialMessageComputableV1
import WideExactInitialMessageComputableV4
import WideExactInitialInverseV5
import WideExactInitialInverseBridgeV2
import WideExactInitialCirclePairInverseV5
import InitialMessageComputableV8
import FieldInterpolationNodes
import InitialMessageForwardFilterV3
import InitialMessagePublicFilter
import GSInitialMessageCandidateFilter
import WideExactGRSInstantiationV5
import CompPoly.Bivariate.GuruswamiSudan.Core
import CompPoly.Bivariate.GuruswamiSudan.Filter
import CompPoly.Univariate.Roots.Extraction
import CompPoly.Univariate.Roots.Context
import CompPoly.Univariate.Roots.RootProduct
import CompPoly.Univariate.Roots.Backend
import CompPoly.Univariate.Roots.Splitter
import CompPoly.Univariate.Roots.Correctness
import CompPoly.Univariate.Context
import CompPoly.Univariate.BatchEval.SubproductTree
import CompPoly.Univariate.BatchEval.Correctness
import CompPoly.Univariate.BatchEval.Context
import CompPoly.Univariate.Roots.SmoothSubgroup.Basic
import CompPoly.Univariate.Roots.SmoothSubgroup.Correctness
import CompPoly.Univariate.Roots.SmoothSubgroup
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import CompPoly.Univariate.Roots.Enumeration
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots
import CompPoly.Bivariate.GuruswamiSudan.Root.Common
import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas
import CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree
import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
import GSArrayMatchingCount
import GSNormalizedPointAgreement
import GSWideExactAgreementInputs
import RRFinalMessageRecovery
import GSActualEncoderGRSBridge
import GSRuntimeInitialDistanceEncoderBridge
import GSFinalMessageCandidateFilter
import GSRuntimeFinalDistanceEncoderBridge
import GSConcreteReceivedWordPoints
import GSConcreteReceivedWordInputs
import GSInterpolationAgreementCore
import GSInitialActualMessageRecovery
import GSActualRuntimeCloseCompleteness
import LiteralTerminalCandidate
import R1ComputableTraceWitness
import R1TraceValueDecode
import R1TraceWitnessExtract
import R1ListWitnessExtract
import CandidateListWitnessExtract
import LiteralTerminalListExtract
import R1PartialJointList
import R1IncrementalJointCandidates
import R1IncrementalCandidateLoop
import FiniteListCandidateMerge
import GSRuntimeInitialJointKeepCore
import GSConcreteInitialRuntimeJointCandidates
import LiteralComputedCandidateExtract
import GSByteJointSpendExtractor
import RawCutWordsFromRunExecutable
import RawCompiledRunWordStabilityV8
import RawCompiledTranscriptRoundAlignmentV7
import RawChecksCommitmentFormats
import AcceptedAdaptiveFiatShamir
import RawPublicInitRecovery
import RawPublicInitParser
import InitialPublicWalk
import InitialPublicWalkCells
import InitialPublicWalkTrace
import SemanticPublicSelection
import EarlyPublicSelection
import R1UnifiedSemanticFacts
import R1UnifiedSemanticActualView
import R1QueryOwnFollow
import R1PrefixNextTrace
import R1UnifiedSemanticInjection
import R1UnifiedFramework
import R1UnifiedOrdinaryFirstCell
import R1UnifiedSemanticCase
import EarlyPublicExperiment
import R1UnifiedReseedView
import R1ReseedOwnFollow
import R1ReseedTrace
import R1PrefixReseedTrace
import R1UnifiedReseedInjection
import R1UnifiedReseedCase
import EarlyPublicSpecialCases
import R1UnifiedPayloadZero
import R1UnifiedCanonicalProver
import EarlyPublicTotalCase
import RawPublicOpeningWalk

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `WideExactInitialParityCBridgeV9, `WideExactNaturalBasisTriangularV4, `WideExactNaturalBasisTriangularV6, `WideExactNaturalBasisTriangularV8, `WideExactNaturalBasisTriangularV9, `WideExactNaturalBasisTriangularV12, `WideExactNaturalBasisTriangularV14, `WideExactInitialMessageComputableV1, `WideExactInitialMessageComputableV4, `WideExactInitialInverseV5, `WideExactInitialInverseBridgeV2, `WideExactInitialCirclePairInverseV5, `InitialMessageComputableV8, `FieldInterpolationNodes, `InitialMessageForwardFilterV3, `InitialMessagePublicFilter, `GSInitialMessageCandidateFilter, `WideExactGRSInstantiationV5, `CompPoly.Bivariate.GuruswamiSudan.Core, `CompPoly.Bivariate.GuruswamiSudan.Filter, `CompPoly.Univariate.Roots.Extraction, `CompPoly.Univariate.Roots.Context, `CompPoly.Univariate.Roots.RootProduct, `CompPoly.Univariate.Roots.Backend, `CompPoly.Univariate.Roots.Splitter, `CompPoly.Univariate.Roots.Correctness, `CompPoly.Univariate.Context, `CompPoly.Univariate.BatchEval.SubproductTree, `CompPoly.Univariate.BatchEval.Correctness, `CompPoly.Univariate.BatchEval.Context, `CompPoly.Univariate.Roots.SmoothSubgroup.Basic, `CompPoly.Univariate.Roots.SmoothSubgroup.Correctness, `CompPoly.Univariate.Roots.SmoothSubgroup, `CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField, `CompPoly.Univariate.Roots.Enumeration, `CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots, `CompPoly.Bivariate.GuruswamiSudan.Root.Common, `CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas, `CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree, `CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness, `GSArrayMatchingCount, `GSNormalizedPointAgreement, `GSWideExactAgreementInputs, `RRFinalMessageRecovery, `GSActualEncoderGRSBridge, `GSRuntimeInitialDistanceEncoderBridge, `GSFinalMessageCandidateFilter, `GSRuntimeFinalDistanceEncoderBridge, `GSConcreteReceivedWordPoints, `GSConcreteReceivedWordInputs, `GSInterpolationAgreementCore, `GSInitialActualMessageRecovery, `GSActualRuntimeCloseCompleteness, `LiteralTerminalCandidate, `R1ComputableTraceWitness, `R1TraceValueDecode, `R1TraceWitnessExtract, `R1ListWitnessExtract, `CandidateListWitnessExtract, `LiteralTerminalListExtract, `R1PartialJointList, `R1IncrementalJointCandidates, `R1IncrementalCandidateLoop, `FiniteListCandidateMerge, `GSRuntimeInitialJointKeepCore, `GSConcreteInitialRuntimeJointCandidates, `LiteralComputedCandidateExtract, `GSByteJointSpendExtractor, `RawCutWordsFromRunExecutable, `RawCompiledRunWordStabilityV8, `RawCompiledTranscriptRoundAlignmentV7, `RawChecksCommitmentFormats, `AcceptedAdaptiveFiatShamir, `RawPublicInitRecovery, `RawPublicInitParser, `InitialPublicWalk, `InitialPublicWalkCells, `InitialPublicWalkTrace, `SemanticPublicSelection, `EarlyPublicSelection, `R1UnifiedSemanticFacts, `R1UnifiedSemanticActualView, `R1QueryOwnFollow, `R1PrefixNextTrace, `R1UnifiedSemanticInjection, `R1UnifiedFramework, `R1UnifiedOrdinaryFirstCell, `R1UnifiedSemanticCase, `EarlyPublicExperiment, `R1UnifiedReseedView, `R1ReseedOwnFollow, `R1ReseedTrace, `R1PrefixReseedTrace, `R1UnifiedReseedInjection, `R1UnifiedReseedCase, `EarlyPublicSpecialCases, `R1UnifiedPayloadZero, `R1UnifiedCanonicalProver, `EarlyPublicTotalCase, `RawPublicOpeningWalk ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ4_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ4_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ4_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ4_AUDIT_COMPLETE declarations={count} modules={selected.size}"
