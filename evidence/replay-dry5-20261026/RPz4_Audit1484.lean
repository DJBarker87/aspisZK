import Lean
import RawRecordedActualAdaptiveFailureBoundV6
import RawChecksAdaptiveFailureConsumer
import LiteralAdaptiveClassifierHitToDecodedChain
import LiteralNoHitFromTranscriptAlignment
import RawChecksHitFromTransport
import RawChecksAdaptiveCleanModel
import RawChecksAdaptiveFailureNoModel
import RawExtractorCostComposedV2
import HchecksAccumulator
import HchecksReaderComposition
import AspisR1AdapterReconstruct.Types
import AspisR1AdapterReconstruct.FunsExternal
import AspisR1AdapterReconstruct.Funs
import ExtractedAdapterReconstructSuccess
import ExtractedAdapterTransferBindings
import R1PublicByteCodec
import R1PublicByteCodecLaws
import PublicCodecAgreement
import AspisR1PublicSerializer.Types
import AspisR1PublicSerializer.Funs
import PublicSerializerFieldsRefinement431
import PublicSerializerSuccess431
import PublicSerializerFrontier431
import PublicSerializerWhole431
import PublicRawCore
import PublicExtractedRawBridge431
import AspisR1WithdrawalValidation.Types
import AspisR1WithdrawalValidation.Funs
import WithdrawalValidationAmount431
import PublicRawAmountGuard
import WithdrawalCarrierBridge431
import R1PublicSourceRaw
import R1PublicCodecAgreement
import R1PublicSourceRawMap
import R1PublicSourceRawSuccess
import PublicRawCoreAgreement
import PublicRawAmountGuardAgreement
import R1PublicSourceBoundary
import ExtractedPublicCheckedBridge432
import ExtractedAdapterStageBindingObligations
import HchecksPublicComposition
import DecoderInstanceBoundary
import BinMerkle32Path
import BinMerkleNodeCodec
import BinRawByteCollisionTargets
import BinCombinedMerkleCollision
import QueryScanExhaustion
import QueryScanModelFailure
import QvStage1Count
import QvStage2Count
import R1FinalSoundnessNumeric
import R1FinalSoundness
import BinMerkleTable
import BinMerkleRecovery
import BinMerkle32Leaf
import BinMerkleLeafRecovery
import BinMerkleLeafCodec
import BinMerkleRecordedLog
import BinMerkleTraceInputs
import BinMerkleLogRecovery
import BinMerkleProgram
import BinRawByteCutRecovery
import BinMerkleWalkWitness
import BinRecordedRecoveryWitness
import BinMerkleLogExtension
import BinRawByteCutStability
import BinMultiproof
import BinCanonicalCutWords
import BinCompiledRunWordStability
import DecoderInstanceBoundaryBin
import BinThreeCommitmentTypedOpening
import WireBindingRecordCodec
import SharedBinaryRecordGrammar
import BinGrammar
import BinSharedGrammarBridge
import RawCutRecordedWordsExecutableBin
import RawCutWordsFromRunExecutableBin
import RawCutWordsFromRunPublicValidBin
import RawRecordedPublicSpendExtractorCoreBin
import RawRecordedPublicSpendExtractorPublicEqualityBin
import RawRecordedPublicSpendExtractorReturnedRelationBin
import RawRecordedChecksSpendExtractorBin
import RawRecordedPublicSpendExtractorCompletenessBin
import RawRecordedOracleExtractionMassBin
import RawByteTableWordsBin
import LiteralTableWordChoiceBin
import RecordedBinaryExperimentBin
import DecoderQueryAccounting
import BinDecoderInitialStarts
import BinHonestStartFrames
import BinHonestQueryBudget
import R19BudgetSamplerReads
import R1VerifierCallBudget
import R19BudgetOriginalReads
import OracleDecisionFeasibilityBudget
import OracleDecisionPrereqSampler
import OracleDecisionFeasibilityCompiler
import OracleDecisionFeasibilityMerkle
import OracleDecisionFeasibilityBridge
import OracleDecisionPrereqPaths

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RawRecordedActualAdaptiveFailureBoundV6, `RawChecksAdaptiveFailureConsumer, `LiteralAdaptiveClassifierHitToDecodedChain, `LiteralNoHitFromTranscriptAlignment, `RawChecksHitFromTransport, `RawChecksAdaptiveCleanModel, `RawChecksAdaptiveFailureNoModel, `RawExtractorCostComposedV2, `HchecksAccumulator, `HchecksReaderComposition, `AspisR1AdapterReconstruct.Types, `AspisR1AdapterReconstruct.FunsExternal, `AspisR1AdapterReconstruct.Funs, `ExtractedAdapterReconstructSuccess, `ExtractedAdapterTransferBindings, `R1PublicByteCodec, `R1PublicByteCodecLaws, `PublicCodecAgreement, `AspisR1PublicSerializer.Types, `AspisR1PublicSerializer.Funs, `PublicSerializerFieldsRefinement431, `PublicSerializerSuccess431, `PublicSerializerFrontier431, `PublicSerializerWhole431, `PublicRawCore, `PublicExtractedRawBridge431, `AspisR1WithdrawalValidation.Types, `AspisR1WithdrawalValidation.Funs, `WithdrawalValidationAmount431, `PublicRawAmountGuard, `WithdrawalCarrierBridge431, `R1PublicSourceRaw, `R1PublicCodecAgreement, `R1PublicSourceRawMap, `R1PublicSourceRawSuccess, `PublicRawCoreAgreement, `PublicRawAmountGuardAgreement, `R1PublicSourceBoundary, `ExtractedPublicCheckedBridge432, `ExtractedAdapterStageBindingObligations, `HchecksPublicComposition, `DecoderInstanceBoundary, `BinMerkle32Path, `BinMerkleNodeCodec, `BinRawByteCollisionTargets, `BinCombinedMerkleCollision, `QueryScanExhaustion, `QueryScanModelFailure, `QvStage1Count, `QvStage2Count, `R1FinalSoundnessNumeric, `R1FinalSoundness, `BinMerkleTable, `BinMerkleRecovery, `BinMerkle32Leaf, `BinMerkleLeafRecovery, `BinMerkleLeafCodec, `BinMerkleRecordedLog, `BinMerkleTraceInputs, `BinMerkleLogRecovery, `BinMerkleProgram, `BinRawByteCutRecovery, `BinMerkleWalkWitness, `BinRecordedRecoveryWitness, `BinMerkleLogExtension, `BinRawByteCutStability, `BinMultiproof, `BinCanonicalCutWords, `BinCompiledRunWordStability, `DecoderInstanceBoundaryBin, `BinThreeCommitmentTypedOpening, `WireBindingRecordCodec, `SharedBinaryRecordGrammar, `BinGrammar, `BinSharedGrammarBridge, `RawCutRecordedWordsExecutableBin, `RawCutWordsFromRunExecutableBin, `RawCutWordsFromRunPublicValidBin, `RawRecordedPublicSpendExtractorCoreBin, `RawRecordedPublicSpendExtractorPublicEqualityBin, `RawRecordedPublicSpendExtractorReturnedRelationBin, `RawRecordedChecksSpendExtractorBin, `RawRecordedPublicSpendExtractorCompletenessBin, `RawRecordedOracleExtractionMassBin, `RawByteTableWordsBin, `LiteralTableWordChoiceBin, `RecordedBinaryExperimentBin, `DecoderQueryAccounting, `BinDecoderInitialStarts, `BinHonestStartFrames, `BinHonestQueryBudget, `R19BudgetSamplerReads, `R1VerifierCallBudget, `R19BudgetOriginalReads, `OracleDecisionFeasibilityBudget, `OracleDecisionPrereqSampler, `OracleDecisionFeasibilityCompiler, `OracleDecisionFeasibilityMerkle, `OracleDecisionFeasibilityBridge, `OracleDecisionPrereqPaths ]
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
