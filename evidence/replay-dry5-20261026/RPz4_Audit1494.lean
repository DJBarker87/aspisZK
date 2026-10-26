import Lean
import GammaCandidateDecodedFieldRank
import ExtractedMaskReverseRange
import ExtractedMaskPreparedState
import ExtractedMaskPreparedClosure
import ExtractedMaskArrayThree
import ExtractedMaskReducerOps
import ExtractedMaskReducer
import ExtractedMaskCM31Mul
import ExtractedMaskQM31Mul
import ExtractedMaskPreparedComponent
import ExtractedMaskQM31Tower
import ExtractedMaskQM31Exact
import ExtractedMaskPreparedMul
import ExtractedMaskHornerStep
import CurrentSamplerCanonicalV5
import GammaCandidateCanonicalOutput
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
import ExtractedSourceFull25Frames
import ExtractedSourceDigestAddresses
import ExtractedSourceDigestOracle
import Query31ConcreteDriverTraceFacts
import IndexedCandidateOrdinarySampleBridgeV3
import IndexedCandidateOrdinaryRetainedBridgeV5
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
import S2OwnedCurrentCarrierV1
import S2OwnedSnapshotTransportV1
import S2OwnedSourceInstallationV1
import S2SdkOwnedInstallationV1
import S2SdkOwnedReachabilityV1
import S2SdkOwnedDecodedReuseV1
import S2SdkOwnedGuardBodyV1
import S2SdkReadyAcquireV1
import S2SdkReadyStateV1
import S2SdkProofGateModelV1
import S2SdkProofPrefixTotalV1
import S2SdkProofGateTotalV1
import S2SdkGateAdmittedImageV1
import S2SdkProofComparatorV1
import S2SdkSnapshotReferenceV1
import S2SdkSnapshotEquivalenceV1
import S2SdkProofPrefixParentV1
import S2FrameOperationsTotalV1
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
import S2SdkBorrowedEquivalenceV1
import S2SdkProofGateJoinV1
import S2SdkAdmittedCallerV1
import S2SdkLinkedCallerV1
import S2SdkErrorBufferFrameV1
import S2SdkFixedInputCallerV1
import S2SdkCheckpointWriterV1
import S2SdkSavedFirstV1
import S2SdkFixedSavedFirstV1
import S126SdkFixedInputCurrentV1
import S126SdkFixedSavedCurrentV1
import S2SdkMetadataFrameV1
import S126SdkSavedAccountExportV1
import R22Stage2LeafTotal
import S2SdkCheckpointImageV1
import S2SdkFixedImageFirstV1
import S2SdkKeyEqualityV1
import S2E_Types
import S2I_ReturnData
import S2K_Serialization
import S2K_FrontierCases
import S6FiveCodecTypesV1

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `GammaCandidateDecodedFieldRank, `ExtractedMaskReverseRange, `ExtractedMaskPreparedState, `ExtractedMaskPreparedClosure, `ExtractedMaskArrayThree, `ExtractedMaskReducerOps, `ExtractedMaskReducer, `ExtractedMaskCM31Mul, `ExtractedMaskQM31Mul, `ExtractedMaskPreparedComponent, `ExtractedMaskQM31Tower, `ExtractedMaskQM31Exact, `ExtractedMaskPreparedMul, `ExtractedMaskHornerStep, `CurrentSamplerCanonicalV5, `GammaCandidateCanonicalOutput, `AspisC2HostEmbedding.Types, `AspisC2HostEmbedding.Funs, `C2HostEmbedding, `Query31ScanTypesOnly, `Query31ExplicitScanBody, `Query31ExplicitScanConcreteSteps, `Query31ExplicitListLoop, `Query31UnrolledDriverFirstStop, `Query31ModelScanCall, `Query31ModelDriverChain, `TerminalStandardOperationModelsV1, `TerminalArrayFromFnModelV4Clean, `QueryScanConcreteWordsDecoder, `Query31ConcreteWordsDriverChain, `Query31ArrayReadback, `ExtractedSourceFull25Frames, `ExtractedSourceDigestAddresses, `ExtractedSourceDigestOracle, `Query31ConcreteDriverTraceFacts, `IndexedCandidateOrdinarySampleBridgeV3, `IndexedCandidateOrdinaryRetainedBridgeV5, `S6NamedDiscriminantV1, `S6FullForestEncoderNamedTypesV1, `S2OwnedStage1TypesV1, `S2SdkOwnedTypesV1, `S2SdkOwnedModelV1, `S2SdkOwnedPrimitivesTotalV1, `S2SdkOwnedBorrowTotalV1, `S2SdkOwnedGuardReleaseV1, `S2SdkOwnedGuardAcquireV1, `S2SdkOwnedGuardFrameV1, `S2OwnedStage1ModelV1, `S2OwnedStage1ReachabilityV1, `S2OwnedCurrentCarrierV1, `S2OwnedSnapshotTransportV1, `S2OwnedSourceInstallationV1, `S2SdkOwnedInstallationV1, `S2SdkOwnedReachabilityV1, `S2SdkOwnedDecodedReuseV1, `S2SdkOwnedGuardBodyV1, `S2SdkReadyAcquireV1, `S2SdkReadyStateV1, `S2SdkProofGateModelV1, `S2SdkProofPrefixTotalV1, `S2SdkProofGateTotalV1, `S2SdkGateAdmittedImageV1, `S2SdkProofComparatorV1, `S2SdkSnapshotReferenceV1, `S2SdkSnapshotEquivalenceV1, `S2SdkProofPrefixParentV1, `S2FrameOperationsTotalV1, `S2SdkBorrowedReferenceV1, `S2SdkBorrowedBufferFrameV1, `S2SdkSourceIteratorV1, `S2StdAnySourceV1, `S2OwnedCheckpointScanTotalV1, `S2CheckpointGuardTransportV1, `S2StdAnySourceTotalV1, `S2SdkSourceIteratorTotalV1, `S2SdkOwnedScanTotalV1, `S2SdkSourceScanV1, `S2SdkBorrowedScanV1, `S2SdkBorrowedEquivalenceV1, `S2SdkProofGateJoinV1, `S2SdkAdmittedCallerV1, `S2SdkLinkedCallerV1, `S2SdkErrorBufferFrameV1, `S2SdkFixedInputCallerV1, `S2SdkCheckpointWriterV1, `S2SdkSavedFirstV1, `S2SdkFixedSavedFirstV1, `S126SdkFixedInputCurrentV1, `S126SdkFixedSavedCurrentV1, `S2SdkMetadataFrameV1, `S126SdkSavedAccountExportV1, `R22Stage2LeafTotal, `S2SdkCheckpointImageV1, `S2SdkFixedImageFirstV1, `S2SdkKeyEqualityV1, `S2E_Types, `S2I_ReturnData, `S2K_Serialization, `S2K_FrontierCases, `S6FiveCodecTypesV1 ]
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
