import Lean
import Port5Q1_ObservedValue
import Port5Q1_ObservedBasis
import Port5Q1_Observation
import Port5Q1_AdvanceRange
import Port4C_Pending
import Port5Q1_InitialState
import Port5Q1_Block
import Port5Q1_Materialize
import Port5Q1_QueryBlock
import Port5Q1_InitialFields
import Port5Q1_Recurrence
import Port5Q1_Ten
import Op4P_Extract.Types
import Op4P_Extract.Funs
import Op4P_Refinement
import BinLeafLengthWork
import BinLeafBoundedLength
import BinLeafListWork
import FixedWidthDecoderWork
import PublicPrimitiveDecoderWork
import PublicParserWork
import OptionWorkBoundM10
import AbstractStageSpecM10
import AllocationStageSpecM10
import ListConstructorAllocationM10
import BinNodeListWork
import BinMerkleRecoveryReads
import BinLeafBoundedTable
import RawCutRecordedWordsBoundedBin
import BinRecordedRecoveryReads
import BinFrameReplayReads
import RawRecordedPublicSpendExtractorBoundedBin
import BinEagerWordsReads
import ExtractorWorkMonad
import AllocationFoldM10
import PublicCursorAllocationM10
import CompPolyFactorSplitCount
import CompPolyFactorCounted
import CompPolyFactorTotalDivisionCost
import CompPolyFactorRawDivisionBridge
import GSBinaryModPowerWorkM10
import GSScalarCallScheduleM10
import GSScalarSequentialScheduleM10
import GSScalarOperandEnvelopeM10
import GSScalarFactorEnvelopeM10
import ExtractorProofBindM10
import AllocationProofBindM10
import OptionWorkInvariantM10
import AllocationOptionBindM10
import ConstantStagePackM10
import AllocationStageAttachM10
import AllocationConstantStagePackM10
import ExtractorListWorkM10
import FiniteCandidateMergeWorkM10
import AllocationListConsumersM10
import CandidateMergeAllocationM10
import AllocationStageCompositionLawsM10
import StageGuardM10
import OptionReferenceTransportM10
import PublicParserAllocationM10
import ExtractorStagesM10
import AllocationPublicStageM10
import PublicParsedIndexM10
import CountDominanceM10
import StartChargeHit
import ExtractedRecordByteValue
import StrictLowChunkCodec
import ExtractedPrefixFieldAgreement
import ExtractedRecordStrictCodec
import ExtractedRecordStrictLow
import ExtractedPrefixLoopMap
import ExtractedPrefixRecordAgreement
import ExtractedPrefixParserAgreement
import AspisR1RowShape.Types
import AspisR1RowShape.Funs
import ExtractedRowShape
import ExtractedRecordFraming
import RecordPayloadPartition
import ExtractedRecordHighZero
import ExtractedRecordValidator
import ExtractedRecordPayloadSoundness
import ExtractedPrefixStrictPayload
import ExtractedPrefixSemanticLow
import ExtractedPrefixChunkOrder
import ExtractedPrefixCoefficients
import ExtractedPrefixHeaderBytes
import R1RecordLengthCodec
import R1RecordParserModel
import ExtractedPrefixFrameAgreement
import ExtractedPrefixRowPayload
import ExtractedPrefixTypedFull
import AspisR1CircleSampleWrapper.Types
import AspisR1CircleFallback.Types
import AspisR1CircleFallback.FunsExternal
import AspisR1CircleFallback.Funs
import AspisR1CircleSampleWrapper.FunsExternal
import AspisR1CircleSampleWrapper.Funs
import AspisV8R19.InverseFieldSlice
import AspisV8R19.GuardedFieldSlice
import AspisV8R19.ComplexFieldSlice

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `Port5Q1_ObservedValue, `Port5Q1_ObservedBasis, `Port5Q1_Observation, `Port5Q1_AdvanceRange, `Port4C_Pending, `Port5Q1_InitialState, `Port5Q1_Block, `Port5Q1_Materialize, `Port5Q1_QueryBlock, `Port5Q1_InitialFields, `Port5Q1_Recurrence, `Port5Q1_Ten, `Op4P_Extract.Types, `Op4P_Extract.Funs, `Op4P_Refinement, `BinLeafLengthWork, `BinLeafBoundedLength, `BinLeafListWork, `FixedWidthDecoderWork, `PublicPrimitiveDecoderWork, `PublicParserWork, `OptionWorkBoundM10, `AbstractStageSpecM10, `AllocationStageSpecM10, `ListConstructorAllocationM10, `BinNodeListWork, `BinMerkleRecoveryReads, `BinLeafBoundedTable, `RawCutRecordedWordsBoundedBin, `BinRecordedRecoveryReads, `BinFrameReplayReads, `RawRecordedPublicSpendExtractorBoundedBin, `BinEagerWordsReads, `ExtractorWorkMonad, `AllocationFoldM10, `PublicCursorAllocationM10, `CompPolyFactorSplitCount, `CompPolyFactorCounted, `CompPolyFactorTotalDivisionCost, `CompPolyFactorRawDivisionBridge, `GSBinaryModPowerWorkM10, `GSScalarCallScheduleM10, `GSScalarSequentialScheduleM10, `GSScalarOperandEnvelopeM10, `GSScalarFactorEnvelopeM10, `ExtractorProofBindM10, `AllocationProofBindM10, `OptionWorkInvariantM10, `AllocationOptionBindM10, `ConstantStagePackM10, `AllocationStageAttachM10, `AllocationConstantStagePackM10, `ExtractorListWorkM10, `FiniteCandidateMergeWorkM10, `AllocationListConsumersM10, `CandidateMergeAllocationM10, `AllocationStageCompositionLawsM10, `StageGuardM10, `OptionReferenceTransportM10, `PublicParserAllocationM10, `ExtractorStagesM10, `AllocationPublicStageM10, `PublicParsedIndexM10, `CountDominanceM10, `StartChargeHit, `ExtractedRecordByteValue, `StrictLowChunkCodec, `ExtractedPrefixFieldAgreement, `ExtractedRecordStrictCodec, `ExtractedRecordStrictLow, `ExtractedPrefixLoopMap, `ExtractedPrefixRecordAgreement, `ExtractedPrefixParserAgreement, `AspisR1RowShape.Types, `AspisR1RowShape.Funs, `ExtractedRowShape, `ExtractedRecordFraming, `RecordPayloadPartition, `ExtractedRecordHighZero, `ExtractedRecordValidator, `ExtractedRecordPayloadSoundness, `ExtractedPrefixStrictPayload, `ExtractedPrefixSemanticLow, `ExtractedPrefixChunkOrder, `ExtractedPrefixCoefficients, `ExtractedPrefixHeaderBytes, `R1RecordLengthCodec, `R1RecordParserModel, `ExtractedPrefixFrameAgreement, `ExtractedPrefixRowPayload, `ExtractedPrefixTypedFull, `AspisR1CircleSampleWrapper.Types, `AspisR1CircleFallback.Types, `AspisR1CircleFallback.FunsExternal, `AspisR1CircleFallback.Funs, `AspisR1CircleSampleWrapper.FunsExternal, `AspisR1CircleSampleWrapper.Funs, `AspisV8R19.InverseFieldSlice, `AspisV8R19.GuardedFieldSlice, `AspisV8R19.ComplexFieldSlice ]
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
