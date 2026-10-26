import Lean
import DecoderFiniteStartSupport
import BinInitialQueryAccounting
import OracleDecisionPrereqStarts
import OracleDecisionPrereqLog
import OracleDecisionMultiTree
import OracleDecisionMultiBuild
import OracleDecisionPrereqExact
import OracleDecisionMultiAccounting
import OraclePortExperiment
import RawDigestLogCarrier
import QueryScanAbortAccounting
import R9TwoTransactionExperiment
import R9DeployedBinaryExperiment
import R9PoolCheckpointCodec
import R1FinalSoundnessNumericBin
import BinPerQueryNumeric
import RawRecordedActualAdaptiveFailureBoundBin
import RawCompiledChecksOriginalScheduleBin
import RawChecksAdaptiveCleanModelBin
import RawChecksAdaptiveFailureNoModelBin
import RawRecordedExtractorBranchTrace
import RawExtractorParameterPolynomial
import RawExtractorCostComposedBin
import RawRecordedExtractorBranchTraceBin
import RawRecordedLogCostObstruction
import RawRecordedInitialCutObstruction
import RawRecordedLogLengthBin
import R1FinalSoundnessBinPerQuery
import R1LiteralQuerySample
import QueryScanRow31SourcePlacement
import R1FinalSoundnessBinPerQueryR18
import R15WriterModel
import R16DecisionCheckpoint
import R9PoolSavedTenModel
import OraclePortCheckpoint
import OraclePortCheckpointStateC3
import OraclePortHeader
import R1FinalSoundnessBinPerQueryR19
import R16DecisionErasure
import R16CanonReduction
import R16CanonExtractor
import R16CanonRecorded
import OraclePortCanon
import R16DecisionQueryModel
import D0ScheduleAdmission
import D0InstanceAdmission
import RWireRawBoundedCollision
import RWireLiteralLegacyDecoderCompletion
import RWireRawLiteralDecoderCompletion
import RWireRawFullPublicSelection
import RWireRawLiteralDecoderRestore
import RWireRawCutLiteralSamplerOrder
import RWireRawCutLiteralNextFrame
import RWireRawCutLiteralRowZeroOrder
import RWireRawCutLiteralReseedOrder
import RWireRawCutLiteralQueryOrder
import RWireRawCutLiteralQueryAdjacent
import RWireRawCutLiteralAllFrames
import RWireConstructedWords
import RWireMerkleNodeLookupExt
import RWireMerkleNodeRecordUnique
import RWireMerkleLeafLookupExt
import RWireMerkleLeafRecordUnique
import RWireMerkleLogExt
import RWireRawByteCutTable
import RWireRawByteTableWords
import RWireRawByteLaterTableWords
import RWireRawCutLaterTableLiteralWords
import RWireLiteralTableChoiceWords
import RWireRawLiteralRecordedDecoder
import RWireRawFullPublicRun
import RWireRawCompiledTranscript
import RWireRawLiteralCompiledDecoder
import RWireRawCompiledDecoderCompletion
import RWireRawAdaptiveCompiledCompletion
import RWireCheckedFormat
import RWireInitialTag
import RWireCompletion
import RWireCounterexamples
import InitialTagDecision
import OraclePortAdmission
import OraclePortReplay
import OraclePortWords
import OraclePortSchedule
import OraclePortCleanModel
import OraclePortConsumer
import R3SemanticEquationCore
import R3SemanticRemainingJoins
import D0TypedChecks
import OraclePortChecks
import OraclePortCompactDraft
import OraclePortPhysicalFrameDraft
import OraclePortCheckpointAbiC5
import OraclePortCheckpointSlicesC5
import OraclePortCheckpointResumeC5
import OraclePortCheckpointPreparedC5
import OraclePortCheckpointOracleC5
import OraclePortCkptAbiCodec
import OraclePortCkptAbiReference
import OracleDecisionMultiRecovery

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `DecoderFiniteStartSupport, `BinInitialQueryAccounting, `OracleDecisionPrereqStarts, `OracleDecisionPrereqLog, `OracleDecisionMultiTree, `OracleDecisionMultiBuild, `OracleDecisionPrereqExact, `OracleDecisionMultiAccounting, `OraclePortExperiment, `RawDigestLogCarrier, `QueryScanAbortAccounting, `R9TwoTransactionExperiment, `R9DeployedBinaryExperiment, `R9PoolCheckpointCodec, `R1FinalSoundnessNumericBin, `BinPerQueryNumeric, `RawRecordedActualAdaptiveFailureBoundBin, `RawCompiledChecksOriginalScheduleBin, `RawChecksAdaptiveCleanModelBin, `RawChecksAdaptiveFailureNoModelBin, `RawRecordedExtractorBranchTrace, `RawExtractorParameterPolynomial, `RawExtractorCostComposedBin, `RawRecordedExtractorBranchTraceBin, `RawRecordedLogCostObstruction, `RawRecordedInitialCutObstruction, `RawRecordedLogLengthBin, `R1FinalSoundnessBinPerQuery, `R1LiteralQuerySample, `QueryScanRow31SourcePlacement, `R1FinalSoundnessBinPerQueryR18, `R15WriterModel, `R16DecisionCheckpoint, `R9PoolSavedTenModel, `OraclePortCheckpoint, `OraclePortCheckpointStateC3, `OraclePortHeader, `R1FinalSoundnessBinPerQueryR19, `R16DecisionErasure, `R16CanonReduction, `R16CanonExtractor, `R16CanonRecorded, `OraclePortCanon, `R16DecisionQueryModel, `D0ScheduleAdmission, `D0InstanceAdmission, `RWireRawBoundedCollision, `RWireLiteralLegacyDecoderCompletion, `RWireRawLiteralDecoderCompletion, `RWireRawFullPublicSelection, `RWireRawLiteralDecoderRestore, `RWireRawCutLiteralSamplerOrder, `RWireRawCutLiteralNextFrame, `RWireRawCutLiteralRowZeroOrder, `RWireRawCutLiteralReseedOrder, `RWireRawCutLiteralQueryOrder, `RWireRawCutLiteralQueryAdjacent, `RWireRawCutLiteralAllFrames, `RWireConstructedWords, `RWireMerkleNodeLookupExt, `RWireMerkleNodeRecordUnique, `RWireMerkleLeafLookupExt, `RWireMerkleLeafRecordUnique, `RWireMerkleLogExt, `RWireRawByteCutTable, `RWireRawByteTableWords, `RWireRawByteLaterTableWords, `RWireRawCutLaterTableLiteralWords, `RWireLiteralTableChoiceWords, `RWireRawLiteralRecordedDecoder, `RWireRawFullPublicRun, `RWireRawCompiledTranscript, `RWireRawLiteralCompiledDecoder, `RWireRawCompiledDecoderCompletion, `RWireRawAdaptiveCompiledCompletion, `RWireCheckedFormat, `RWireInitialTag, `RWireCompletion, `RWireCounterexamples, `InitialTagDecision, `OraclePortAdmission, `OraclePortReplay, `OraclePortWords, `OraclePortSchedule, `OraclePortCleanModel, `OraclePortConsumer, `R3SemanticEquationCore, `R3SemanticRemainingJoins, `D0TypedChecks, `OraclePortChecks, `OraclePortCompactDraft, `OraclePortPhysicalFrameDraft, `OraclePortCheckpointAbiC5, `OraclePortCheckpointSlicesC5, `OraclePortCheckpointResumeC5, `OraclePortCheckpointPreparedC5, `OraclePortCheckpointOracleC5, `OraclePortCkptAbiCodec, `OraclePortCkptAbiReference, `OracleDecisionMultiRecovery ]
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
