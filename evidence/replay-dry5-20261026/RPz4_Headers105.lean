import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalMerkleCollision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalMerkleCollision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalMerkleRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalMerkleRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1InitialWalkCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1InitialWalkCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1DuplexRecordPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1DuplexRecordPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1QueryMissingFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1QueryMissingFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1TableStateSeparation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1TableStateSeparation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1OpeningWalk.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1OpeningWalk"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ReseedPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ReseedPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPowersCallback.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPowersCallback"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytes3Word.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytes3Word"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbiReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbiReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_RowLoop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_RowLoop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Physical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Physical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalFrozenLevels.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalFrozenLevels"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeCountLevels.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeCountLevels"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalAddress.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalAddress"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalLive.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalLive"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeNodeWindow.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeNodeWindow"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_SliceIndex.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_SliceIndex"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_PreparedClaim.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_PreparedClaim"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/IndexedCandidateGeneratedLoopBridgeV4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "IndexedCandidateGeneratedLoopBridgeV4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1WideToBytesSource/TypesExternal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1WideToBytesSource.TypesExternal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/P6ChunksExactMutModelV3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6ChunksExactMutModelV3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ClaimOwnedOuterStepV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ClaimOwnedOuterStepV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6OuterNativeCodecV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6OuterNativeCodecV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6OuterNativeHelpersV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6OuterNativeHelpersV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozen2Roots.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozen2Roots"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_LeafStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_LeafStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPowersCallbackInvariant.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPowersCallbackInvariant"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GammaCallerExplicitHelpers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GammaCallerExplicitHelpers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/IndexedCandidateAddSmallLoopCanonicalV11.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "IndexedCandidateAddSmallLoopCanonicalV11"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedMaskReducer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedMaskReducer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimOuterSum.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimOuterSum"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishDotLoopCount.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishDotLoopCount"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S5QRaw/EbyKPushActualRawCoefficientBoundsV10.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S5QRaw.EbyKPushActualRawCoefficientBoundsV10"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R22RawQmProductResiduesV15.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R22RawQmProductResiduesV15"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S5CanonicalProductRangesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S5CanonicalProductRangesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1EbyKPushWideToQ.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1EbyKPushWideToQ"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1FinishDotReturnedDecodedValueV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1FinishDotReturnedDecodedValueV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimScalarNormalForm.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimScalarNormalForm"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentFinishEquality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentFinishEquality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishFieldSelectorAdapterV2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishFieldSelectorAdapterV2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimRangeStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimRangeStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishCandidateDotSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishCandidateDotSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EbyKNewCutProof.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EbyKNewCutProof"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EbyKPushExplicitTypesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EbyKPushExplicitTypesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EbyKFinishTotal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EbyKFinishTotal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideProduct.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideProduct"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideMulM31V13.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideMulM31V13"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishCandidateEquations.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishCandidateEquations"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EbyKCheckedQCanonicality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EbyKCheckedQCanonicality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1EbyKPushConcreteCheckedQV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1EbyKPushConcreteCheckedQV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/DotPushSourceResidues.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DotPushSourceResidues"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_PreparedAbsorbAssociation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_PreparedAbsorbAssociation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedPublicPreparationSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPublicPreparationSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedDecoderCallerBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedDecoderCallerBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedWithdrawalCallerPublic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedWithdrawalCallerPublic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeRead32.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeRead32"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeLevelIteration.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeLevelIteration"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortReachedRootsC6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortReachedRootsC6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1DecodeKFullParserCanonicalityCMQ.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1DecodeKFullParserCanonicalityCMQ"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryReadPairProgramV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryReadPairProgramV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryFinishProgramV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryFinishProgramV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryMaterializeModelV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryMaterializeModelV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryAbsorbProgramV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryAbsorbProgramV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryByteChainBudgetV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryByteChainBudgetV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1NativeCompactOrdinaryPrefixV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1NativeCompactOrdinaryPrefixV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/Chord.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.Chord"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/FunctionalWeights.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.FunctionalWeights"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/RootCounts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.RootCounts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/Fold.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.Fold"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/ResponseSelection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.ResponseSelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/JointList.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.JointList"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/MatchedInstances.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.MatchedInstances"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/RoundNormalization.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.RoundNormalization"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/RoundCore.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.RoundCore"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_PhysicalLevels.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_PhysicalLevels"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawPublicInitRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawPublicInitRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/InitialPublicWalkTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "InitialPublicWalkTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedSemanticFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedSemanticFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedSemanticActualView.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedSemanticActualView"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PrefixNextTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PrefixNextTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PrefixReseedTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PrefixReseedTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1OpeningPrefixAnchor.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1OpeningPrefixAnchor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1QueryOwnFollow.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1QueryOwnFollow"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1QueryAnswersFirstRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1QueryAnswersFirstRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedOpeningRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedOpeningRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedOpeningView.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedOpeningView"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PrefixQueryTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PrefixQueryTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedRhoInjection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedRhoInjection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/FactorMonic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Bivariate.FactorMonic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/Context.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Bivariate.GuruswamiSudan.Context"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRConcreteState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRConcreteState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Deriv.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.Deriv"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.ToMathlib.Polynomial.BivariateMultiplicity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/LinearAlgebra/Dense/Basic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.LinearAlgebra.Dense.Basic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/LinearAlgebra/Dense/RowOps.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.LinearAlgebra.Dense.RowOps"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/LinearAlgebra/Dense/RowOpsCorrectness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.LinearAlgebra.Dense.RowOpsCorrectness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/LinearAlgebra/Dense/RrefSemantics.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.LinearAlgebra.Dense.RrefSemantics"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
