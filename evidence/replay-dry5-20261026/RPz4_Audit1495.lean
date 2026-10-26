import Lean
import S6StdOptionSourceV1
import S6FullSourceCodecV1
import S6AfterstateDecoderFactoredV1
import S6ByteInverseV1
import S6SourceWordInverseV1
import S6SourceDigestDecodeTotalV1
import S6DigestReferenceV1
import S6RetainedDigestTotalV1
import S6SourceDigestTotalV1
import S6SliceFrameLengthV1
import S6SliceFrameContentsV1
import S6EightChunkFrameV1
import S6SourceDigestEncodeContentsV1
import S6SourceDigestRoundtripV1
import S6SourceDigestAcceptedInverseV1
import S6StdByteArrayTotalV1
import S6SourcePaymentValidatorTotalV1
import S6SourcePaymentDecodeHelpersV1
import S6SourcePaymentCommonDecodeV1
import S6StdByteSliceEqualityV1
import S6SourceCanonicalTotalV1
import S6SourceSnapshotValidatorTotalV1
import S6SourceAfterstateValidatorTotalV1
import S6SourceAfterstateDecodeHelpersV1
import S6AfterstateDecoderPart16TotalV1
import S6AfterstateDecoderPart12TotalV1
import S6AfterstateDecoderPart8TotalV1
import S6AfterstateDecoderPart4TotalV1
import S6AfterstateDecoderPart0TotalV1
import S6SourceAfterstateDecodeTotalV1
import S6AfterstateDecoderFramesV1
import S6AfterstateFramePrependV1
import S6AfterstateDecoderPart12FramesV1
import S6AfterstateDecoderPart8FramesV1
import S6AfterstateDecoderPart4FramesV1
import S6AfterstateDecoderPart0FramesV1
import S6SourceAfterstateDecodedFramesV1
import S6SourceAfterstateAcceptedFramesV1
import S6SourcePaymentHeaderTotalV1
import S6SourcePaymentDecodeTotalV1
import S6SourcePaymentDecodedFramesV1
import S6PointWriteFrameV1
import S6PaymentCommonChunkFrameV1
import S6SourcePaymentCommonContentsV1
import S6SliceRecomposeV1
import S6PaymentFrameRecomposeV1
import S6AfterstateFrameBytesV1
import S6AfterstateWriteFramesV1
import S6NativeSliceFrameLengthV1
import S6NativeLateWordReadV1
import S6LateWriteFramesV1
import S6ShortSlicesV1
import S6FullForestEncoderNamedNativeV1
import S6PaymentTailChunkFrameV1
import S6ZeroWordBytesV1
import S6OuterWriteFramesV1
import S6CurrentBoxedDecoderSourceV1
import S6CurrentVerifierCarrierV1
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

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `S6StdOptionSourceV1, `S6FullSourceCodecV1, `S6AfterstateDecoderFactoredV1, `S6ByteInverseV1, `S6SourceWordInverseV1, `S6SourceDigestDecodeTotalV1, `S6DigestReferenceV1, `S6RetainedDigestTotalV1, `S6SourceDigestTotalV1, `S6SliceFrameLengthV1, `S6SliceFrameContentsV1, `S6EightChunkFrameV1, `S6SourceDigestEncodeContentsV1, `S6SourceDigestRoundtripV1, `S6SourceDigestAcceptedInverseV1, `S6StdByteArrayTotalV1, `S6SourcePaymentValidatorTotalV1, `S6SourcePaymentDecodeHelpersV1, `S6SourcePaymentCommonDecodeV1, `S6StdByteSliceEqualityV1, `S6SourceCanonicalTotalV1, `S6SourceSnapshotValidatorTotalV1, `S6SourceAfterstateValidatorTotalV1, `S6SourceAfterstateDecodeHelpersV1, `S6AfterstateDecoderPart16TotalV1, `S6AfterstateDecoderPart12TotalV1, `S6AfterstateDecoderPart8TotalV1, `S6AfterstateDecoderPart4TotalV1, `S6AfterstateDecoderPart0TotalV1, `S6SourceAfterstateDecodeTotalV1, `S6AfterstateDecoderFramesV1, `S6AfterstateFramePrependV1, `S6AfterstateDecoderPart12FramesV1, `S6AfterstateDecoderPart8FramesV1, `S6AfterstateDecoderPart4FramesV1, `S6AfterstateDecoderPart0FramesV1, `S6SourceAfterstateDecodedFramesV1, `S6SourceAfterstateAcceptedFramesV1, `S6SourcePaymentHeaderTotalV1, `S6SourcePaymentDecodeTotalV1, `S6SourcePaymentDecodedFramesV1, `S6PointWriteFrameV1, `S6PaymentCommonChunkFrameV1, `S6SourcePaymentCommonContentsV1, `S6SliceRecomposeV1, `S6PaymentFrameRecomposeV1, `S6AfterstateFrameBytesV1, `S6AfterstateWriteFramesV1, `S6NativeSliceFrameLengthV1, `S6NativeLateWordReadV1, `S6LateWriteFramesV1, `S6ShortSlicesV1, `S6FullForestEncoderNamedNativeV1, `S6PaymentTailChunkFrameV1, `S6ZeroWordBytesV1, `S6OuterWriteFramesV1, `S6CurrentBoxedDecoderSourceV1, `S6CurrentVerifierCarrierV1, `S1M31EmbeddingSourceV1, `P6ChunksExactMutModelV3, `AspisR1WideToBytesSource.TypesExternal, `AspisR1WideToBytesSource.Types, `AspisR1WideToBytesSource.FunsExternal, `AspisR1WideToBytesSource.Funs, `ToBytesP6StepsV3, `ToBytesP6ActiveBodyV12, `ToBytesP6StateInvariantV1, `PaintBlocksPrefixV1, `PaintSourceLimbsV1, `ToBytesP6OutputInvariantV1, `AspisR1WideToBytesIndexedCandidate.Types, `AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions, `AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11, `ToBytesP6IndexedCarrierBridgeV1, `S1NativeCompactTypesV1, `S1NativeCompactModelV1, `S1LoopSafetyV1, `S1NativeCompactFrameV1, `S1NativeCompactBodyFrameV1, `S1NativeCompactLoopFrameV1, `S1NativeCompactRootV1, `S1NativeCompactLengthsV1, `S1NativeCompactEntryLengthV1, `S1PrepareBufferRecombineV1, `S1PrepareExpansionBuffersV1, `ExtractedPrefixRecordStep, `ExtractedPrefixTrace, `ExtractedPrefixParse, `S1NativeCompactCopyPrefixV1, `S1NativeCompactOrdinaryPrefixV1, `S1NativeCompactThreeRowsV1, `S1NativeCompactPrefix79V1, `S1AcceptedSliceRangeV1, `S1ValuesOwnedTypesV1, `S1ValuesOwnedModelV1, `S1ValuesOwnedFrameV1, `S1ValuesOwnedInstallationV1, `S1PrepareBufferY1RecombineV1, `S1PrepareBothBuffersV1, `S1ValuesOwnedStepTotalV1 ]
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
