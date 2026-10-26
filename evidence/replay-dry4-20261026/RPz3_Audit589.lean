import Lean
import IndexedCandidateAddSmallLoopCanonicalV11
import IndexedCandidateAddSmallNatModelV1
import IndexedCandidateAddSmallWrapperNatModelV3
import R1Z.ProverCommitArrayIndex25
import IndexedCandidateDecode8RetainedBridgeV3
import AspisC2HostEmbedding.Types
import AspisC2HostEmbedding.Funs
import C2HostEmbedding
import Query31ScanTypesOnly
import Query31ExplicitScanBody
import Query31ExplicitScanConcreteSteps
import Query31ExplicitListLoop
import Query31UnrolledDriverFirstStop
import Query31ModelScanCall
import Query31ModelDriverChain
import TerminalStandardOperationModelsV1
import TerminalArrayFromFnModelV4Clean
import QueryScanConcreteWordsDecoder
import Query31ConcreteWordsDriverChain
import Query31ArrayReadback
import Query31ConcreteDriverTraceFacts
import S6NamedDiscriminantV1
import S6FullForestEncoderNamedTypesV1
import S2OwnedStage1TypesV1
import S2SdkOwnedTypesV1
import S2SdkOwnedModelV1
import S2SdkOwnedPrimitivesTotalV1
import S2SdkOwnedBorrowTotalV1
import S2SdkOwnedGuardReleaseV1
import S2SdkOwnedGuardAcquireV1
import S2SdkOwnedGuardFrameV1
import S2OwnedStage1ModelV1
import S2OwnedStage1ReachabilityV1
import S2OwnedSnapshotTransportV1
import S2SdkSnapshotReferenceV1
import S2SdkSnapshotEquivalenceV1
import S2SdkBorrowedReferenceV1
import S2SdkBorrowedBufferFrameV1
import S2SdkSourceIteratorV1
import S2StdAnySourceV1
import S2OwnedCheckpointScanTotalV1
import S2CheckpointGuardTransportV1
import S2StdAnySourceTotalV1
import S2SdkSourceIteratorTotalV1
import S2SdkOwnedScanTotalV1
import S2SdkSourceScanV1
import S2SdkBorrowedScanV1
import S2E_Types
import S2I_ReturnData
import S2K_Serialization
import S2K_FrontierCases
import S6FiveCodecTypesV1
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

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `IndexedCandidateAddSmallLoopCanonicalV11, `IndexedCandidateAddSmallNatModelV1, `IndexedCandidateAddSmallWrapperNatModelV3, `R1Z.ProverCommitArrayIndex25, `IndexedCandidateDecode8RetainedBridgeV3, `AspisC2HostEmbedding.Types, `AspisC2HostEmbedding.Funs, `C2HostEmbedding, `Query31ScanTypesOnly, `Query31ExplicitScanBody, `Query31ExplicitScanConcreteSteps, `Query31ExplicitListLoop, `Query31UnrolledDriverFirstStop, `Query31ModelScanCall, `Query31ModelDriverChain, `TerminalStandardOperationModelsV1, `TerminalArrayFromFnModelV4Clean, `QueryScanConcreteWordsDecoder, `Query31ConcreteWordsDriverChain, `Query31ArrayReadback, `Query31ConcreteDriverTraceFacts, `S6NamedDiscriminantV1, `S6FullForestEncoderNamedTypesV1, `S2OwnedStage1TypesV1, `S2SdkOwnedTypesV1, `S2SdkOwnedModelV1, `S2SdkOwnedPrimitivesTotalV1, `S2SdkOwnedBorrowTotalV1, `S2SdkOwnedGuardReleaseV1, `S2SdkOwnedGuardAcquireV1, `S2SdkOwnedGuardFrameV1, `S2OwnedStage1ModelV1, `S2OwnedStage1ReachabilityV1, `S2OwnedSnapshotTransportV1, `S2SdkSnapshotReferenceV1, `S2SdkSnapshotEquivalenceV1, `S2SdkBorrowedReferenceV1, `S2SdkBorrowedBufferFrameV1, `S2SdkSourceIteratorV1, `S2StdAnySourceV1, `S2OwnedCheckpointScanTotalV1, `S2CheckpointGuardTransportV1, `S2StdAnySourceTotalV1, `S2SdkSourceIteratorTotalV1, `S2SdkOwnedScanTotalV1, `S2SdkSourceScanV1, `S2SdkBorrowedScanV1, `S2E_Types, `S2I_ReturnData, `S2K_Serialization, `S2K_FrontierCases, `S6FiveCodecTypesV1, `S6StdOptionSourceV1, `S6FullSourceCodecV1, `S6AfterstateDecoderFactoredV1, `S6ByteInverseV1, `S6SourceWordInverseV1, `S6SourceDigestDecodeTotalV1, `S6DigestReferenceV1, `S6RetainedDigestTotalV1, `S6SourceDigestTotalV1, `S6SliceFrameLengthV1, `S6SliceFrameContentsV1, `S6EightChunkFrameV1, `S6SourceDigestEncodeContentsV1, `S6SourceDigestRoundtripV1, `S6SourceDigestAcceptedInverseV1, `S6StdByteArrayTotalV1, `S6SourcePaymentValidatorTotalV1, `S6SourcePaymentDecodeHelpersV1, `S6SourcePaymentCommonDecodeV1, `S6StdByteSliceEqualityV1, `S6SourceCanonicalTotalV1, `S6SourceSnapshotValidatorTotalV1, `S6SourceAfterstateValidatorTotalV1, `S6SourceAfterstateDecodeHelpersV1, `S6AfterstateDecoderPart16TotalV1, `S6AfterstateDecoderPart12TotalV1, `S6AfterstateDecoderPart8TotalV1, `S6AfterstateDecoderPart4TotalV1, `S6AfterstateDecoderPart0TotalV1, `S6SourceAfterstateDecodeTotalV1, `S6AfterstateDecoderFramesV1, `S6AfterstateFramePrependV1, `S6AfterstateDecoderPart12FramesV1, `S6AfterstateDecoderPart8FramesV1, `S6AfterstateDecoderPart4FramesV1, `S6AfterstateDecoderPart0FramesV1, `S6SourceAfterstateDecodedFramesV1, `S6SourceAfterstateAcceptedFramesV1, `S6SourcePaymentHeaderTotalV1, `S6SourcePaymentDecodeTotalV1, `S6SourcePaymentDecodedFramesV1, `S6PointWriteFrameV1, `S6PaymentCommonChunkFrameV1, `S6SourcePaymentCommonContentsV1, `S6SliceRecomposeV1, `S6PaymentFrameRecomposeV1, `S6AfterstateFrameBytesV1, `S6AfterstateWriteFramesV1 ]
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
