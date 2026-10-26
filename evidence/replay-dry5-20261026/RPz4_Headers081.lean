import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_GeometryModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_GeometryModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_MapPoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_MapPoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_SelectedCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_SelectedCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_FlatPoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_FlatPoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_WordShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_WordShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op3I_Std.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op3I_Std"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_ExpandedChildren.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_ExpandedChildren"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_FirstOccurrence.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_FirstOccurrence"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-op4-p6-20261025/Op4P_Extract/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op4P_Extract.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeCompactScan.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeCompactScan"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeSliceComposition.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeSliceComposition"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_Control.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_Control"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Marks.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Marks"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/VTop_SecondFlow.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "VTop_SecondFlow"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/VTop_Run.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "VTop_Run"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortRouteIndexC4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortRouteIndexC4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortStoredLeafRecoveryC4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortStoredLeafRecoveryC4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Scheduled.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Scheduled"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_LiteralTop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_LiteralTop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_SuccessOracle.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_SuccessOracle"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_ChildJoins.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_ChildJoins"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_Observation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_Observation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_SavedIdentities.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_SavedIdentities"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCheckpointStateC3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCheckpointStateC3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortPhysicalFrameDraft.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortPhysicalFrameDraft"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SelectedFieldSequenceCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SelectedFieldSequenceCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_WriterBody.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_WriterBody"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_ClaimsCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_ClaimsCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_SemanticClaims.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_SemanticClaims"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_SemanticDecode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_SemanticDecode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_InputY.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_InputY"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_DecodeCircleIndex.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_DecodeCircleIndex"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_GammaY.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_GammaY"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_SelectedScalar.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_SelectedScalar"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_OriginalClaim.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_OriginalClaim"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_PreparedRemaining.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_PreparedRemaining"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_CircleProjection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_CircleProjection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_CoordinateShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_CoordinateShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_ContextCoordinates.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_ContextCoordinates"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_InactivePhysicalMeaning.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_InactivePhysicalMeaning"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_MatchingFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_MatchingFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_TypedRows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_TypedRows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_CircleValues.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_CircleValues"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_OpeningReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_OpeningReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_WriterPreparedScalar.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_WriterPreparedScalar"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_ChallengeTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_ChallengeTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_SamplerPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_SamplerPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_SemanticChallenges.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_SemanticChallenges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedSourceDigestAddresses.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedSourceDigestAddresses"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-sem-20261025/RawSourceLiteralSamplerStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawSourceLiteralSamplerStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralTypedWords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralTypedWords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS2/Statement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS2.Statement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1GenericProgramRenameMass.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1GenericProgramRenameMass"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_ClosedGamma.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_ClosedGamma"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_ClosedOrdinary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_ClosedOrdinary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FixedWidthDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FixedWidthDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FixedWidthDecodedSlices.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FixedWidthDecodedSlices"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1WideExactLimbCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1WideExactLimbCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ListFieldCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ListFieldCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_FlushState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_FlushState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortRepresentativeCountC3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortRepresentativeCountC3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortDataChoiceDraft.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortDataChoiceDraft"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_LowRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_LowRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1NativeCompactEntryLengthV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1NativeCompactEntryLengthV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticCarrierV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticCarrierV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticVerifyReachabilityV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticVerifyReachabilityV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticRootCopyV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticRootCopyV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/SemanticRoundAlphaSelectedCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SemanticRoundAlphaSelectedCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/StrictLowChunkCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "StrictLowChunkCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RecordPayloadPartition.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RecordPayloadPartition"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedPrefixParserAgreement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixParserAgreement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedRecordFraming.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedRecordFraming"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1RetainedFieldByteCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RetainedFieldByteCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralSemanticDensity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralSemanticDensity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralCircleEvents.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralCircleEvents"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralOpeningDensity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralOpeningDensity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralQueryDensity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralQueryDensity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralRhoDensity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralRhoDensity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ConcretePackBasis.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ConcretePackBasis"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1GenericNoHitFS2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1GenericNoHitFS2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SpendRelation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SpendRelation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QueryScanStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QueryScanStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31ScanTypesOnly.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31ScanTypesOnly"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31ExplicitScanConcreteSteps.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31ExplicitScanConcreteSteps"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_QuerySelection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_QuerySelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1QueryFirstRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1QueryFirstRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_OpeningCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_OpeningCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_QueryLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_QueryLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PreparedScalarEffectsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PreparedScalarEffectsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_QueryAbsorber.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_QueryAbsorber"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_QueryJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_QueryJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_OpeningSampler.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_OpeningSampler"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_ScalarCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_ScalarCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_LimbBytes.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_LimbBytes"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_InactiveDecode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_InactiveDecode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PreparedScalarErasureV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PreparedScalarErasureV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentOriginalPreparedNativeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentOriginalPreparedNativeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1CurrentOwnedConcreteJoinV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1CurrentOwnedConcreteJoinV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_BlockCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_BlockCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
