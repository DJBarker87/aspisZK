import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/Root/FieldRoots/FiniteField.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Roots/Enumeration.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.Roots.Enumeration"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WideExactInitialMessageComputableV4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WideExactInitialMessageComputableV4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WideExactInitialInverseBridgeV2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WideExactInitialInverseBridgeV2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WideExactInitialCirclePairInverseV5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WideExactInitialCirclePairInverseV5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRVectorRowNonzeroV5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRVectorRowNonzeroV5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRFiniteCoeffScannerV9.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRFiniteCoeffScannerV9"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRInitialFullRowsScanFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRInitialFullRowsScanFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRInitialNonzeroRowBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRInitialNonzeroRowBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRInitialDroppedModelBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRInitialDroppedModelBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRChildNormalization.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRChildNormalization"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRPrefixCollector.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRPrefixCollector"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRConcreteNormalizeChildTotal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRConcreteNormalizeChildTotal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRConcreteChildrenProgram.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRConcreteChildrenProgram"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRBoundedSliceScannerV5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRBoundedSliceScannerV5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRConcreteTraversal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRConcreteTraversal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/SequentialFiniteTapeLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SequentialFiniteTapeLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WideExactNaturalBasisTriangularV8.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WideExactNaturalBasisTriangularV8"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Scheduled.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Scheduled"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/FinalRoot.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.FinalRoot"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPolyPolynomialBackendBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPolyPolynomialBackendBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CantorZassenhausFastTrial.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CantorZassenhausFastTrial"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31AcceptFiber.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31AcceptFiber"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FSRetryOutputUniformity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FSRetryOutputUniformity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31RetryMassNatCard.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31RetryMassNatCard"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PoseidonMap.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PoseidonMap"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ParsedTargetsFirstHit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ParsedTargetsFirstHit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R22Stage2LocalBodies.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R22Stage2LocalBodies"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R22Stage2ControlBounds.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R22Stage2ControlBounds"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_SdkAccepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_SdkAccepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalLogicalStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalLogicalStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalObservations.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalObservations"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ClaimOwnedInnerCompleteV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ClaimOwnedInnerCompleteV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6OuterEncodeFromDecodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6OuterEncodeFromDecodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6OuterByteLayoutV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6OuterByteLayoutV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6OuterAcceptedCalleesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6OuterAcceptedCalleesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeForestDecodedLayoutV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeForestDecodedLayoutV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6OuterNativeInstalledV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6OuterNativeInstalledV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeLateEncodeTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeLateEncodeTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_PhysicalCalls.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_PhysicalCalls"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimPartsUpdates.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimPartsUpdates"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S5QRaw/ActualCoefficientsFromBoundsV2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S5QRaw.ActualCoefficientsFromBoundsV2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1EbyKDotPushSourceV1/LoopAdapter.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1EbyKDotPushSourceV1.LoopAdapter"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OriginalDotPushRawLoopToLiteralV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OriginalDotPushRawLoopToLiteralV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1FinishDotReturnedProductWords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1FinishDotReturnedProductWords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WeightsFieldExplicitDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WeightsFieldExplicitDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishCandidateDotTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishCandidateDotTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1Stage2Accumulate/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1Stage2Accumulate.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1EbyKFinish/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1EbyKFinish.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CanonicalDotFinishSemantics.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CanonicalDotFinishSemantics"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishCandidateRoundSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishCandidateRoundSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1EbyKPushExplicitOpsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1EbyKPushExplicitOpsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/DotPushWordSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DotPushWordSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_VerifyAssociation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_VerifyAssociation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1WithdrawalCaller/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1WithdrawalCaller.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedTerminalDecoderSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedTerminalDecoderSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryMaterializePairsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryMaterializePairsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryOverwriteEightV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryOverwriteEightV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/PolynomialPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.PolynomialPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/ChordDegree.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.ChordDegree"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_PhysicalNode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_PhysicalNode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_PhysicalBind.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_PhysicalBind"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPolyFiniteRootSampler.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPolyFiniteRootSampler"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPolyGeneralRootsProgram.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPolyGeneralRootsProgram"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRVectorNormalizedCompleteV3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRVectorNormalizedCompleteV3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRScannedNormalizedTransition.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRScannedNormalizedTransition"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRRootDescent.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRRootDescent"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRVectorActualScannerV2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRVectorActualScannerV2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRSubstitutionTailBound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRSubstitutionTailBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
