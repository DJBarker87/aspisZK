import Lean
import RPz7_S6NativeSnapshotReadArrayV1
import RPz7_S6NativeSnapshotDecoderFactoredV1
import RPz7_S6NativeSnapshotDecodeHelpersV1
import RPz7_S6NativeSnapshotDecoderFramesV1
import RPz7_S6NativeSnapshotFramePrependV1
import RPz7_S6NativeSnapshotDecoderPart12FramesV1
import RPz7_S6NativeSnapshotDecoderPart8FramesV1
import RPz7_S6NativeSnapshotDecoderPart4FramesV1
import RPz7_S6NativeSnapshotDecoderPart0FramesV1
import RPz7_S6NativeSnapshotDecodedFramesV1
import RPz7_S6NativeSnapshotDecodeTotalV1
import RPz7_S6NativeSnapshotAcceptedFramesV1
import RPz7_S6NativeSnapshotEncoderGraphV1
import RPz7_S6NativeSnapshotFrontierContentsV1
import RPz7_S6NativeSnapshotPrepareContentsV1
import RPz7_S6NativeSnapshotDecodedLayoutV1
import RPz7_S6NativeSnapshotEncodeSuccessV1
import RPz7_S6NativeSnapshotCodecV1
import RPz7_S6NativeLateEncodeTotalV1
import RPz7_S6NativeLateChildDecodeV1
import RPz7_S6NativeLateDecoderFactoredV1
import RPz7_S6NativeLateDecodeTotalV1
import RPz7_S6NativeLateWordCastV1
import RPz7_S6NativeLateWordConstantsV1
import RPz7_S6NativeLateDecoderSplitV1
import RPz7_S6NativeLateTailFramesV1
import RPz7_S6NativeLateDecodedFramesV1
import RPz7_S6NativeLateAcceptedFramesV1
import RPz7_S6NativeLateAcceptedValidityV1
import RPz7_S6NativeLateChildEncodeV1
import RPz7_S6NativeLateEncodeAcceptedV1
import RPz7_S6NativeLateEncodeSuccessV1
import RPz7_S6NativeLateHeaderLayoutV1
import RPz7_S6NativeLateHeaderWritesV1
import RPz7_S6NativeLateEncoderContentsV1
import RPz7_S6NativeLateCodecV1
import RPz7_S6OuterCarrierBridgeV1
import RPz7_S6NativePaymentValidatorTotalV1
import RPz7_S6NativePaymentCommonEncodeTotalV1
import RPz7_S6NativePaymentEncodeTotalV1
import RPz7_S6NativeForestHelpersV1
import RPz7_S6NativeForestValidatorTotalV1
import RPz7_S6OuterNativeOpsV1
import RPz7_S6OuterNativeReturnsV1
import RPz7_S6OuterNativeInstalledV1
import RPz7_S6NativePaymentDecodeHelpersV1
import RPz7_S6NativePaymentCommonDecodeV1
import RPz7_S6NativePaymentHeaderTotalV1
import RPz7_S6NativePaymentDecodeTotalV1
import RPz7_S6NativePaymentDecodedFramesV1
import RPz7_S6NativePaymentCommonContentsV1
import RPz7_S6NativePaymentFrameRecomposeV1
import RPz7_S6NativePaymentCommonOutputV1
import RPz7_S6NativePaymentWriterContentsV1
import RPz7_S6NativePaymentAcceptedInverseV1
import RPz7_S6NativePaymentRoundtripV1
import RPz7_S6NativeForestDecodeHelpersV1
import RPz7_S6NativeForestCommonDecodeV1
import RPz7_S6NativeForestPaymentBoxesV1
import RPz7_S6NativeForestDecodeTotalV1
import RPz7_S6NativeForestDecodedFramesV1
import RPz7_S6NativeForestAcceptedFramesV1
import RPz7_S6OuterAcceptedCalleesV1
import RPz7_S6OuterNativeTotalCalleesV1
import RPz7_S6OuterNativeHelpersV1
import RPz7_S6OuterNativeDigestTotalV1
import RPz7_S6OuterNativeEncodeTotalV1
import RPz7_S6OuterEncodeSuccessV1
import RPz7_S6OuterEncodeFromDecodeV1
import RPz7_S6OuterByteLayoutV1
import RPz7_S6OuterEncoderContentsV1
import RPz7_S6NativeForestDecodedLayoutV1
import RPz7_S6OuterAcceptedByteJoinV1
import RPz7_S6OuterNativeCodecV1
import RPz7_S6CurrentAdapterCarrierV1
import RPz7_S6CurrentCodecInstallationV1
import RPz7_S6CurrentCodecTotalV1
import RPz7_S6CurrentStage1CodecJoinV1
import RPz7_S6CurrentVerifierCarrierV1
import RPz7_S6CurrentFirstInstallationV1
import RPz7_S6CurrentStage1FirstJoinV1
import RPz7_S1CurrentOwnedPreparedJoinV1
import RPz7_S1M31EmbeddingTotalV1
import RPz7_S1QueryTraceEmbeddingV1

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_S6NativeSnapshotReadArrayV1, `RPz7_S6NativeSnapshotDecoderFactoredV1, `RPz7_S6NativeSnapshotDecodeHelpersV1, `RPz7_S6NativeSnapshotDecoderFramesV1, `RPz7_S6NativeSnapshotFramePrependV1, `RPz7_S6NativeSnapshotDecoderPart12FramesV1, `RPz7_S6NativeSnapshotDecoderPart8FramesV1, `RPz7_S6NativeSnapshotDecoderPart4FramesV1, `RPz7_S6NativeSnapshotDecoderPart0FramesV1, `RPz7_S6NativeSnapshotDecodedFramesV1, `RPz7_S6NativeSnapshotDecodeTotalV1, `RPz7_S6NativeSnapshotAcceptedFramesV1, `RPz7_S6NativeSnapshotEncoderGraphV1, `RPz7_S6NativeSnapshotFrontierContentsV1, `RPz7_S6NativeSnapshotPrepareContentsV1, `RPz7_S6NativeSnapshotDecodedLayoutV1, `RPz7_S6NativeSnapshotEncodeSuccessV1, `RPz7_S6NativeSnapshotCodecV1, `RPz7_S6NativeLateEncodeTotalV1, `RPz7_S6NativeLateChildDecodeV1, `RPz7_S6NativeLateDecoderFactoredV1, `RPz7_S6NativeLateDecodeTotalV1, `RPz7_S6NativeLateWordCastV1, `RPz7_S6NativeLateWordConstantsV1, `RPz7_S6NativeLateDecoderSplitV1, `RPz7_S6NativeLateTailFramesV1, `RPz7_S6NativeLateDecodedFramesV1, `RPz7_S6NativeLateAcceptedFramesV1, `RPz7_S6NativeLateAcceptedValidityV1, `RPz7_S6NativeLateChildEncodeV1, `RPz7_S6NativeLateEncodeAcceptedV1, `RPz7_S6NativeLateEncodeSuccessV1, `RPz7_S6NativeLateHeaderLayoutV1, `RPz7_S6NativeLateHeaderWritesV1, `RPz7_S6NativeLateEncoderContentsV1, `RPz7_S6NativeLateCodecV1, `RPz7_S6OuterCarrierBridgeV1, `RPz7_S6NativePaymentValidatorTotalV1, `RPz7_S6NativePaymentCommonEncodeTotalV1, `RPz7_S6NativePaymentEncodeTotalV1, `RPz7_S6NativeForestHelpersV1, `RPz7_S6NativeForestValidatorTotalV1, `RPz7_S6OuterNativeOpsV1, `RPz7_S6OuterNativeReturnsV1, `RPz7_S6OuterNativeInstalledV1, `RPz7_S6NativePaymentDecodeHelpersV1, `RPz7_S6NativePaymentCommonDecodeV1, `RPz7_S6NativePaymentHeaderTotalV1, `RPz7_S6NativePaymentDecodeTotalV1, `RPz7_S6NativePaymentDecodedFramesV1, `RPz7_S6NativePaymentCommonContentsV1, `RPz7_S6NativePaymentFrameRecomposeV1, `RPz7_S6NativePaymentCommonOutputV1, `RPz7_S6NativePaymentWriterContentsV1, `RPz7_S6NativePaymentAcceptedInverseV1, `RPz7_S6NativePaymentRoundtripV1, `RPz7_S6NativeForestDecodeHelpersV1, `RPz7_S6NativeForestCommonDecodeV1, `RPz7_S6NativeForestPaymentBoxesV1, `RPz7_S6NativeForestDecodeTotalV1, `RPz7_S6NativeForestDecodedFramesV1, `RPz7_S6NativeForestAcceptedFramesV1, `RPz7_S6OuterAcceptedCalleesV1, `RPz7_S6OuterNativeTotalCalleesV1, `RPz7_S6OuterNativeHelpersV1, `RPz7_S6OuterNativeDigestTotalV1, `RPz7_S6OuterNativeEncodeTotalV1, `RPz7_S6OuterEncodeSuccessV1, `RPz7_S6OuterEncodeFromDecodeV1, `RPz7_S6OuterByteLayoutV1, `RPz7_S6OuterEncoderContentsV1, `RPz7_S6NativeForestDecodedLayoutV1, `RPz7_S6OuterAcceptedByteJoinV1, `RPz7_S6OuterNativeCodecV1, `RPz7_S6CurrentAdapterCarrierV1, `RPz7_S6CurrentCodecInstallationV1, `RPz7_S6CurrentCodecTotalV1, `RPz7_S6CurrentStage1CodecJoinV1, `RPz7_S6CurrentVerifierCarrierV1, `RPz7_S6CurrentFirstInstallationV1, `RPz7_S6CurrentStage1FirstJoinV1, `RPz7_S1CurrentOwnedPreparedJoinV1, `RPz7_S1M31EmbeddingTotalV1, `RPz7_S1QueryTraceEmbeddingV1 ]
  let phaseOwners : Array Name := #[ `RPz7_S1SemanticPrefixModelV1, `RPz7_S1SemanticFinishModelV1, `RPz7_S1SemanticFinishBoundsV1, `RPz7_ClaimsUnrolledFinish, `RPz7_S1SemanticVerifyReachabilityV1, `RPz7_S1SemanticFinishRootsV1, `RPz7_S1AcceptedSemanticNumericV1, `RPz7_S1AcceptedChallengesNumericV1, `RPz7_S1SemanticCodeFinishV1, `RPz7_S1SemanticCodeVerifyV1, `RPz7_S1SemanticCodeFinishExactV1, `RPz7_S1SemanticCodeVerifyExactV1, `RPz7_GExp_FinishAssociation, `RPz7_GExp_VerifyAssociation, `RPz7_S1SemanticBudgetV1, `RPz7_AuS1_Semantic3, `RPz7_F3V_SemanticFinish, `RPz7_F3V_SemanticVerify, `RPz7_RawJ_VerifyRead, `RPz7_RawK_VerifyHead, `RPz7_F3U_VerifyHead ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ7_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ7_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ7_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        if phaseOwners.contains owner || n.toString.startsWith "RPz7_PhaseIso" || n.toString == "AspisR1.Rc10_Top.deployed" then
          logInfo m!"RPZ7_KERNEL_TYPE {(Json.mkObj [("name", toJson n.toString), ("type", toJson (repr c.type).pretty)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ7_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ7_AUDIT_COMPLETE declarations={count} modules={selected.size}"
