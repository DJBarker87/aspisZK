import Lean
import RPz7_CurrentPreparedOrdinaryRankV1
import RPz7_CurrentPreparedJointRankPrefix
import RPz7_CurrentPreparedJointRankTrace
import RPz7_CurrentPreparedJointRankMeaning
import RPz7_PreparedSourcePowersJointRankV1
import RPz7_PreparedSourcePowersEntryV1
import RPz7_PreparedParsedInactiveV1
import RPz7_SelectedWideViewInactiveV1
import RPz7_SelectedWideViewPreparedEntryV1
import RPz7_CurrentCompactInstalledPreparationV1
import RPz7_CurrentOriginalPreparedNativeV1
import RPz7_CurrentOriginalPreparedCarrierTransportV1
import RPz7_CurrentOriginalPreparedInstallationV1
import RPz7_S1BorrowedClaimPreparedBoundaryV1
import RPz7_S1BorrowedClaimFirstCallerV1
import RPz7_S2SdkOwnedGuardBodyV1
import RPz7_S2SdkReadyAcquireV1
import RPz7_S2SdkReadyStateV1
import RPz7_S2SdkGateAdmittedImageV1
import RPz7_S2SdkProofGateJoinV1
import RPz7_S2SdkAdmittedCallerV1
import RPz7_S2SdkLinkedCallerV1
import RPz7_S2SdkErrorBufferFrameV1
import RPz7_S2SdkFixedInputCallerV1
import RPz7_S2SdkCheckpointWriterV1
import RPz7_S2SdkSavedFirstV1
import RPz7_S2SdkFixedSavedFirstV1
import RPz7_S126SdkFixedInputCurrentV1
import RPz7_S126SdkFixedSavedCurrentV1
import RPz7_S2SdkMetadataFrameV1
import RPz7_S126SdkSavedAccountExportV1
import RPz7_ExtractedTx1Reachability
import RPz7_Tx1FinalLenBoundV8
import RPz7_S2SdkCheckpointSizeTotalV1
import RPz7_S2SdkCheckpointLengthV1
import RPz7_S2SdkSizedSavedFirstV1
import RPz7_S126SdkSizedAccountExportV1
import RPz7_S2SdkCheckpointImageV1
import RPz7_S2SdkFixedImageFirstV1
import RPz7_S126SdkAccountImageExportV1
import RPz7_S2SdkKeyEqualityV1
import RPz7_S2SdkReadyCallerV1
import RPz7_S2SdkReadyBodyV1
import RPz7_S2SdkReadyStatementV1
import RPz7_S2SdkReadyOriginalV1
import RPz7_S2SdkReadyRawInputsV1
import RPz7_S2A_InstalledCuts
import RPz7_S2G_InstalledValues
import RPz7_S2K_SourceStore
import RPz7_S2K_SourcePorts
import RPz7_S2K_LoopStep
import RPz7_S2K_Iterator
import RPz7_S2K_DigestTotal
import RPz7_S2K_AfterstateLoop
import RPz7_S2K_AfterstatePrefix
import RPz7_S2K_AfterstateStatus
import RPz7_S2K_DigestBytes
import RPz7_S2K_AfterstateBytes
import RPz7_S2K_AfterstatePrepare
import RPz7_S2K_AfterstateEncoding
import RPz7_S6NativeAfterstateEncoderReuseV1
import RPz7_S6NativeAfterstateDecoderFactoredV1
import RPz7_S6NativeWordSourceBindingV1
import RPz7_S6NativeAfterstateValidatorTotalV1
import RPz7_S6NativeDigestDecodeBindingV1
import RPz7_S6NativeDigestByteContentsV1
import RPz7_S6NativeDigestAcceptedInverseV1
import RPz7_S6NativeDigestEncodeSourceEqV1
import RPz7_S6NativeAfterstateDecodeHelpersV1
import RPz7_S6NativeAfterstateDecoderFramesV1
import RPz7_S6NativeAfterstateFramePrependV1
import RPz7_S6NativeAfterstateDecoderPart12FramesV1
import RPz7_S6NativeAfterstateDecoderPart8FramesV1
import RPz7_S6NativeAfterstateDecoderPart4FramesV1
import RPz7_S6NativeAfterstateDecoderPart0FramesV1
import RPz7_S6NativeAfterstateDecodedFramesV1
import RPz7_S6NativeAfterstateContentsV1
import RPz7_S6NativeAfterstateCodecV1
import RPz7_S6NativeSnapshotStoreV1
import RPz7_S6NativeSnapshotLoopStepV1
import RPz7_S6NativeSnapshotLoopV1
import RPz7_S6NativeSnapshotValidatorTotalV1
import RPz7_S6NativeSnapshotEncodeTotalV1
import RPz7_S6NativeSnapshotReadDigestV1

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_CurrentPreparedOrdinaryRankV1, `RPz7_CurrentPreparedJointRankPrefix, `RPz7_CurrentPreparedJointRankTrace, `RPz7_CurrentPreparedJointRankMeaning, `RPz7_PreparedSourcePowersJointRankV1, `RPz7_PreparedSourcePowersEntryV1, `RPz7_PreparedParsedInactiveV1, `RPz7_SelectedWideViewInactiveV1, `RPz7_SelectedWideViewPreparedEntryV1, `RPz7_CurrentCompactInstalledPreparationV1, `RPz7_CurrentOriginalPreparedNativeV1, `RPz7_CurrentOriginalPreparedCarrierTransportV1, `RPz7_CurrentOriginalPreparedInstallationV1, `RPz7_S1BorrowedClaimPreparedBoundaryV1, `RPz7_S1BorrowedClaimFirstCallerV1, `RPz7_S2SdkOwnedGuardBodyV1, `RPz7_S2SdkReadyAcquireV1, `RPz7_S2SdkReadyStateV1, `RPz7_S2SdkGateAdmittedImageV1, `RPz7_S2SdkProofGateJoinV1, `RPz7_S2SdkAdmittedCallerV1, `RPz7_S2SdkLinkedCallerV1, `RPz7_S2SdkErrorBufferFrameV1, `RPz7_S2SdkFixedInputCallerV1, `RPz7_S2SdkCheckpointWriterV1, `RPz7_S2SdkSavedFirstV1, `RPz7_S2SdkFixedSavedFirstV1, `RPz7_S126SdkFixedInputCurrentV1, `RPz7_S126SdkFixedSavedCurrentV1, `RPz7_S2SdkMetadataFrameV1, `RPz7_S126SdkSavedAccountExportV1, `RPz7_ExtractedTx1Reachability, `RPz7_Tx1FinalLenBoundV8, `RPz7_S2SdkCheckpointSizeTotalV1, `RPz7_S2SdkCheckpointLengthV1, `RPz7_S2SdkSizedSavedFirstV1, `RPz7_S126SdkSizedAccountExportV1, `RPz7_S2SdkCheckpointImageV1, `RPz7_S2SdkFixedImageFirstV1, `RPz7_S126SdkAccountImageExportV1, `RPz7_S2SdkKeyEqualityV1, `RPz7_S2SdkReadyCallerV1, `RPz7_S2SdkReadyBodyV1, `RPz7_S2SdkReadyStatementV1, `RPz7_S2SdkReadyOriginalV1, `RPz7_S2SdkReadyRawInputsV1, `RPz7_S2A_InstalledCuts, `RPz7_S2G_InstalledValues, `RPz7_S2K_SourceStore, `RPz7_S2K_SourcePorts, `RPz7_S2K_LoopStep, `RPz7_S2K_Iterator, `RPz7_S2K_DigestTotal, `RPz7_S2K_AfterstateLoop, `RPz7_S2K_AfterstatePrefix, `RPz7_S2K_AfterstateStatus, `RPz7_S2K_DigestBytes, `RPz7_S2K_AfterstateBytes, `RPz7_S2K_AfterstatePrepare, `RPz7_S2K_AfterstateEncoding, `RPz7_S6NativeAfterstateEncoderReuseV1, `RPz7_S6NativeAfterstateDecoderFactoredV1, `RPz7_S6NativeWordSourceBindingV1, `RPz7_S6NativeAfterstateValidatorTotalV1, `RPz7_S6NativeDigestDecodeBindingV1, `RPz7_S6NativeDigestByteContentsV1, `RPz7_S6NativeDigestAcceptedInverseV1, `RPz7_S6NativeDigestEncodeSourceEqV1, `RPz7_S6NativeAfterstateDecodeHelpersV1, `RPz7_S6NativeAfterstateDecoderFramesV1, `RPz7_S6NativeAfterstateFramePrependV1, `RPz7_S6NativeAfterstateDecoderPart12FramesV1, `RPz7_S6NativeAfterstateDecoderPart8FramesV1, `RPz7_S6NativeAfterstateDecoderPart4FramesV1, `RPz7_S6NativeAfterstateDecoderPart0FramesV1, `RPz7_S6NativeAfterstateDecodedFramesV1, `RPz7_S6NativeAfterstateContentsV1, `RPz7_S6NativeAfterstateCodecV1, `RPz7_S6NativeSnapshotStoreV1, `RPz7_S6NativeSnapshotLoopStepV1, `RPz7_S6NativeSnapshotLoopV1, `RPz7_S6NativeSnapshotValidatorTotalV1, `RPz7_S6NativeSnapshotEncodeTotalV1, `RPz7_S6NativeSnapshotReadDigestV1 ]
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
