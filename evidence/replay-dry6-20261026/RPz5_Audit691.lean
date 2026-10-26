import Lean
import T2Nat_ScalarJoin
import T2Nat_ReadCongr
import T2Nat_Try
import T2Nat_QueryReads
import T2Nat_ReaderSuffix
import T2Nat_AfterQueries
import T2Nat_QuerySource
import T2Nat_ReaderFission
import T2Nat_ReaderPrefix
import T2Nat_ReaderBody
import T2Nat_WeightsCongr
import T2Nat_WeightLoop
import T2Nat_WeightSequence
import T2Nat_SemanticJoin
import T2Nat_ReaderOps
import T2Nat_SuffixJoin
import T2Nat_QueryJoin
import T2Nat_ScalarStage
import T2Nat_RawStage
import T2Nat_TailFactor
import T2Nat_TailJoin
import OraclePortRefineJoinConsumer
import OraclePortRefineJoinExtractionTransport
import OraclePortFrozen2Transport
import OraclePortStoredProbabilityModelC7
import OraclePortHeadlineLedgerC7
import BinTableWork
import RecoveryParserAllocationM10
import BinTypedCacheWork
import BinTypedWordDemandWork
import SharedFiniteMaterializationM10
import BinRecoveryWork
import BinCutRecoveryWork
import BinFrameSizeBound
import BinEagerRecoveryWork
import AllocationBatchM10
import AllocationBatchConstantM10
import GSPointBatchWorkM10
import GSByteSamplerWorkM10
import GSPointSamplerAllocationM10
import GSStoredRowsEnvelopeM10
import RRRowConstructionWorkM10
import GSInterpolationMatrixWorkM10
import GSDensePivotScanCost
import GSDenseRowUpdateCountedCost
import GSDenseNormalizeCellCount
import GSDenseRrefLoopFullWorkCost
import GSDenseKernelExtractionCost
import GSInterpolationNormalizationWorkM10
import GSDenseKernelBasisExtractionCost
import ExtractorFixedWidthResourcesM10
import GSDenseKernelResourcesM10
import GSInterpolationFullWorkM10
import InterpolationAllocationM10
import TypedCacheAllocationM10
import RRNormalizationWorkM10
import RRRowAllocationM10
import GSScalarRootEnvelopeM10
import GSBinaryModPowerFieldWorkM10
import GSScalarTraceFieldWorkM10
import GSScalarConstructorAllocationM10
import GSScalarAtCursorM10
import ExtractorProgramWorkM10
import RRTraversalWriterM10
import RRConcreteWriterM10
import RRActualScalarTraceM10
import GSScalarAtBoundsM10
import GSScalarJobsM10
import RRActualScalarTraceBoundsM10
import RRReachableStorageM10
import RRNodeTariffM10
import RRActualFieldEnvelopeM10
import RRActualTraversalWorkM10
import RRRecoveryWorkM10
import RRTraversalAllocationM10
import GSProtocolBasisSizesM10
import GSProtocolBasisMirrorM10
import GSDecoderActualBankM10
import RRCandidateShapeM10
import GSBankOutputEnvelopeM10
import GSByteBankWorkM10
import GSBankAllocationM10
import BankStageLawsM10
import BankStageSpecM10
import GSByteBankAllocationM10
import GSByteBankAllocationLawsM10
import GSByteBankAllocationStageM10
import MaterializationAllocationM10
import InitialEncoderScheduleM10
import GSPostProcessWorkM10
import InitialPublicImageWorkM10
import PublicImageAllocationM10
import CachedWitnessHashM10
import CachedWitnessAllocationM10
import GSPostProcessCompleteM10
import PostProcessAllocationM10
import PointStageSpecM10
import PostStageSpecM10
import BankEagerEquationM10
import ContinuationReferenceM10

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `T2Nat_ScalarJoin, `T2Nat_ReadCongr, `T2Nat_Try, `T2Nat_QueryReads, `T2Nat_ReaderSuffix, `T2Nat_AfterQueries, `T2Nat_QuerySource, `T2Nat_ReaderFission, `T2Nat_ReaderPrefix, `T2Nat_ReaderBody, `T2Nat_WeightsCongr, `T2Nat_WeightLoop, `T2Nat_WeightSequence, `T2Nat_SemanticJoin, `T2Nat_ReaderOps, `T2Nat_SuffixJoin, `T2Nat_QueryJoin, `T2Nat_ScalarStage, `T2Nat_RawStage, `T2Nat_TailFactor, `T2Nat_TailJoin, `OraclePortRefineJoinConsumer, `OraclePortRefineJoinExtractionTransport, `OraclePortFrozen2Transport, `OraclePortStoredProbabilityModelC7, `OraclePortHeadlineLedgerC7, `BinTableWork, `RecoveryParserAllocationM10, `BinTypedCacheWork, `BinTypedWordDemandWork, `SharedFiniteMaterializationM10, `BinRecoveryWork, `BinCutRecoveryWork, `BinFrameSizeBound, `BinEagerRecoveryWork, `AllocationBatchM10, `AllocationBatchConstantM10, `GSPointBatchWorkM10, `GSByteSamplerWorkM10, `GSPointSamplerAllocationM10, `GSStoredRowsEnvelopeM10, `RRRowConstructionWorkM10, `GSInterpolationMatrixWorkM10, `GSDensePivotScanCost, `GSDenseRowUpdateCountedCost, `GSDenseNormalizeCellCount, `GSDenseRrefLoopFullWorkCost, `GSDenseKernelExtractionCost, `GSInterpolationNormalizationWorkM10, `GSDenseKernelBasisExtractionCost, `ExtractorFixedWidthResourcesM10, `GSDenseKernelResourcesM10, `GSInterpolationFullWorkM10, `InterpolationAllocationM10, `TypedCacheAllocationM10, `RRNormalizationWorkM10, `RRRowAllocationM10, `GSScalarRootEnvelopeM10, `GSBinaryModPowerFieldWorkM10, `GSScalarTraceFieldWorkM10, `GSScalarConstructorAllocationM10, `GSScalarAtCursorM10, `ExtractorProgramWorkM10, `RRTraversalWriterM10, `RRConcreteWriterM10, `RRActualScalarTraceM10, `GSScalarAtBoundsM10, `GSScalarJobsM10, `RRActualScalarTraceBoundsM10, `RRReachableStorageM10, `RRNodeTariffM10, `RRActualFieldEnvelopeM10, `RRActualTraversalWorkM10, `RRRecoveryWorkM10, `RRTraversalAllocationM10, `GSProtocolBasisSizesM10, `GSProtocolBasisMirrorM10, `GSDecoderActualBankM10, `RRCandidateShapeM10, `GSBankOutputEnvelopeM10, `GSByteBankWorkM10, `GSBankAllocationM10, `BankStageLawsM10, `BankStageSpecM10, `GSByteBankAllocationM10, `GSByteBankAllocationLawsM10, `GSByteBankAllocationStageM10, `MaterializationAllocationM10, `InitialEncoderScheduleM10, `GSPostProcessWorkM10, `InitialPublicImageWorkM10, `PublicImageAllocationM10, `CachedWitnessHashM10, `CachedWitnessAllocationM10, `GSPostProcessCompleteM10, `PostProcessAllocationM10, `PointStageSpecM10, `PostStageSpecM10, `BankEagerEquationM10, `ContinuationReferenceM10 ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ5_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ5_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ5_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ5_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ5_AUDIT_COMPLETE declarations={count} modules={selected.size}"
