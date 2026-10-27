import Lean
import S6NativeSliceFrameLengthV1
import S6NativeLateWordReadV1
import S6LateWriteFramesV1
import S6ShortSlicesV1
import S6FullForestEncoderNamedNativeV1
import S6PaymentTailChunkFrameV1
import S6ZeroWordBytesV1
import S6OuterWriteFramesV1
import S1M31EmbeddingSourceV1
import P6ChunksExactMutModelV3
import AspisR1WideToBytesSource.TypesExternal
import AspisR1WideToBytesSource.Types
import AspisR1WideToBytesSource.FunsExternal
import AspisR1WideToBytesSource.Funs
import ToBytesP6StepsV3
import ToBytesP6ActiveBodyV12
import ToBytesP6StateInvariantV1
import PaintBlocksPrefixV1
import PaintSourceLimbsV1
import ToBytesP6OutputInvariantV1
import AspisR1WideToBytesIndexedCandidate.Types
import AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions
import AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11
import ToBytesP6IndexedCarrierBridgeV1
import S1NativeCompactTypesV1
import S1NativeCompactModelV1
import S1LoopSafetyV1
import S1NativeCompactFrameV1
import S1NativeCompactBodyFrameV1
import S1NativeCompactLoopFrameV1
import S1NativeCompactRootV1
import S1NativeCompactLengthsV1
import S1NativeCompactEntryLengthV1
import S1PrepareBufferRecombineV1
import S1PrepareExpansionBuffersV1
import ExtractedPrefixRecordStep
import ExtractedPrefixTrace
import ExtractedPrefixParse
import S1NativeCompactCopyPrefixV1
import S1NativeCompactOrdinaryPrefixV1
import S1NativeCompactThreeRowsV1
import S1NativeCompactPrefix79V1
import S1AcceptedSliceRangeV1
import S1ValuesOwnedTypesV1
import S1ValuesOwnedModelV1
import S1ValuesOwnedFrameV1
import S1ValuesOwnedInstallationV1
import S1PrepareBufferY1RecombineV1
import S1PrepareBothBuffersV1
import S1ValuesOwnedStepTotalV1
import S1ValuesOwnedCellV1
import S1ValuesOwnedChunkFormulaV1
import S1FrameArithmeticV1
import S1ValuesOwnedStepBytesV1
import S1ValuesOwnedChunkBytesV1
import S1ValuesOwnedExpansionFormulaV1
import S1ValuesOwnedChunkTotalV1
import S1ValuesOwnedOuterStepTotalV1
import S1ValuesOwnedExpansionBytesV1
import S1ValuesOwnedReferenceBytesV1
import S1ValuesOwnedOuterTotalV1
import S1ValuesOwnedExactV1
import S1ValuesOwnedAcceptedBytesV1
import S1QueryArrayOperationsV1
import S1QueryOverwriteEightV1
import Op3I_Source
import Op3I_Std
import Port4C_OwnedInverse
import Op4P_Extract.Types
import Op4P_Extract.Funs
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
import ExtractorWorkMonad
import AllocationFoldM10
import PublicCursorAllocationM10
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

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `S6NativeSliceFrameLengthV1, `S6NativeLateWordReadV1, `S6LateWriteFramesV1, `S6ShortSlicesV1, `S6FullForestEncoderNamedNativeV1, `S6PaymentTailChunkFrameV1, `S6ZeroWordBytesV1, `S6OuterWriteFramesV1, `S1M31EmbeddingSourceV1, `P6ChunksExactMutModelV3, `AspisR1WideToBytesSource.TypesExternal, `AspisR1WideToBytesSource.Types, `AspisR1WideToBytesSource.FunsExternal, `AspisR1WideToBytesSource.Funs, `ToBytesP6StepsV3, `ToBytesP6ActiveBodyV12, `ToBytesP6StateInvariantV1, `PaintBlocksPrefixV1, `PaintSourceLimbsV1, `ToBytesP6OutputInvariantV1, `AspisR1WideToBytesIndexedCandidate.Types, `AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions, `AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11, `ToBytesP6IndexedCarrierBridgeV1, `S1NativeCompactTypesV1, `S1NativeCompactModelV1, `S1LoopSafetyV1, `S1NativeCompactFrameV1, `S1NativeCompactBodyFrameV1, `S1NativeCompactLoopFrameV1, `S1NativeCompactRootV1, `S1NativeCompactLengthsV1, `S1NativeCompactEntryLengthV1, `S1PrepareBufferRecombineV1, `S1PrepareExpansionBuffersV1, `ExtractedPrefixRecordStep, `ExtractedPrefixTrace, `ExtractedPrefixParse, `S1NativeCompactCopyPrefixV1, `S1NativeCompactOrdinaryPrefixV1, `S1NativeCompactThreeRowsV1, `S1NativeCompactPrefix79V1, `S1AcceptedSliceRangeV1, `S1ValuesOwnedTypesV1, `S1ValuesOwnedModelV1, `S1ValuesOwnedFrameV1, `S1ValuesOwnedInstallationV1, `S1PrepareBufferY1RecombineV1, `S1PrepareBothBuffersV1, `S1ValuesOwnedStepTotalV1, `S1ValuesOwnedCellV1, `S1ValuesOwnedChunkFormulaV1, `S1FrameArithmeticV1, `S1ValuesOwnedStepBytesV1, `S1ValuesOwnedChunkBytesV1, `S1ValuesOwnedExpansionFormulaV1, `S1ValuesOwnedChunkTotalV1, `S1ValuesOwnedOuterStepTotalV1, `S1ValuesOwnedExpansionBytesV1, `S1ValuesOwnedReferenceBytesV1, `S1ValuesOwnedOuterTotalV1, `S1ValuesOwnedExactV1, `S1ValuesOwnedAcceptedBytesV1, `S1QueryArrayOperationsV1, `S1QueryOverwriteEightV1, `Op3I_Source, `Op3I_Std, `Port4C_OwnedInverse, `Op4P_Extract.Types, `Op4P_Extract.Funs, `BinLeafLengthWork, `BinLeafBoundedLength, `BinLeafListWork, `FixedWidthDecoderWork, `PublicPrimitiveDecoderWork, `PublicParserWork, `OptionWorkBoundM10, `AbstractStageSpecM10, `AllocationStageSpecM10, `ListConstructorAllocationM10, `BinNodeListWork, `BinMerkleRecoveryReads, `BinLeafBoundedTable, `ExtractorWorkMonad, `AllocationFoldM10, `PublicCursorAllocationM10, `ExtractorProofBindM10, `AllocationProofBindM10, `OptionWorkInvariantM10, `AllocationOptionBindM10, `ConstantStagePackM10, `AllocationStageAttachM10, `AllocationConstantStagePackM10, `ExtractorListWorkM10, `FiniteCandidateMergeWorkM10, `AllocationListConsumersM10, `CandidateMergeAllocationM10, `AllocationStageCompositionLawsM10, `StageGuardM10, `OptionReferenceTransportM10 ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ3_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ3_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ3_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ3_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ3_AUDIT_COMPLETE declarations={count} modules={selected.size}"
