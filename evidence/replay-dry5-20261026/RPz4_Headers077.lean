import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_RunInventory.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_RunInventory"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_RunDomain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_RunDomain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_Carrier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_Carrier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_CollectStd.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_CollectStd"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port4c-20261023/Port4C_Pending.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_Pending"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_GeometryInverse.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_GeometryInverse"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_FlushField.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_FlushField"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port4a-20261023/Port4A_Prefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4A_Prefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_WriterShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_WriterShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_ListCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_ListCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_GeometryLine.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_GeometryLine"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_GeometryInverseCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_GeometryInverseCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op3I_Header.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op3I_Header"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_TraceSplice.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_TraceSplice"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-op4-p6-20261025/Op4P_Extract/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op4P_Extract.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeStrictScan.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeStrictScan"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_First.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_First"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Fixture.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Fixture"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/VTop_SecondOrder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "VTop_SecondOrder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortIndexedRecoveryC4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortIndexedRecoveryC4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortPackedChoiceC4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortPackedChoiceC4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortStoredWidthsC4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortStoredWidthsC4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_D189.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_D189"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_R3Top.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_R3Top"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_FinalAudit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_FinalAudit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_FinishConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_FinishConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_PreparedPairing.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_PreparedPairing"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_Returns.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_Returns"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_CurrentNumeric.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_CurrentNumeric"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCheckpointAbiC5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCheckpointAbiC5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_WriterNumeric.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_WriterNumeric"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_ConsDictionary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_ConsDictionary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_SemanticClaimsY.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_SemanticClaimsY"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_SemanticY.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_SemanticY"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_GammaFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_GammaFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_PreparedCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_PreparedCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_SelectedDispatch.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_SelectedDispatch"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_PreparedClaim.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_PreparedClaim"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_PreparedCoordinates.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_PreparedCoordinates"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_InactiveRow28.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_InactiveRow28"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_MatchingInactive.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_MatchingInactive"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_AlignedRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_AlignedRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_CircleEntries.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_CircleEntries"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_CircleReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_CircleReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SourceAlphaValues.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SourceAlphaValues"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SourcePrepared.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SourcePrepared"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SemanticInventory.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SemanticInventory"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_OpeningChallenges.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_OpeningChallenges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_First25Challenges.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_First25Challenges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/RawSourceDigestLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawSourceDigestLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-sem-20261025/RawSourceLiteralTraceLift.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawSourceLiteralTraceLift"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralTranscript.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralTranscript"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ProgramSamplerMap.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ProgramSamplerMap"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_MatchingChallenges.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_MatchingChallenges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_GammaEntry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_GammaEntry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_OrdinaryEntry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_OrdinaryEntry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_QueryArithmetic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_QueryArithmetic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FoldedLeafCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FoldedLeafCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_Advance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_Advance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortSixSlotBudgetC3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortSixSlotBudgetC3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortReaderSourceDraft.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortReaderSourceDraft"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_CircleDecode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_CircleDecode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_SequenceRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_SequenceRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_SubSlice.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_SubSlice"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PrepareBufferRecombineV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PrepareBufferRecombineV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1WideViewVariantV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1WideViewVariantV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticInstallationV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticInstallationV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticAlphaV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticAlphaV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedPrefixSemanticLow.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixSemanticLow"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedPrefixChunkOrder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixChunkOrder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedPrefixHeaderBytes.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixHeaderBytes"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/R1RecordLengthCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RecordLengthCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/R1RecordParserModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RecordParserModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1RecordFrameCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RecordFrameCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SemanticCoefficientCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SemanticCoefficientCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PrefixedStateCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PrefixedStateCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralClassifier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralClassifier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralProtocol.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralProtocol"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS2/Verifier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS2.Verifier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QueryScanLast.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QueryScanLast"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31ModelDriverChain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31ModelDriverChain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31UnrolledDriverFirstStop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31UnrolledDriverFirstStop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31ExplicitListLoop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31ExplicitListLoop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31ExplicitScanBody.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31ExplicitScanBody"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31ModelScanCall.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31ModelScanCall"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_ArrayFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_ArrayFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QueryChain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QueryChain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/R412LegalQueryEnumeration.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.R412LegalQueryEnumeration"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1QuerySampler.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1QuerySampler"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/Q22SamplerProgram.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.Q22SamplerProgram"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_CodeStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_CodeStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_AbsorbCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_AbsorbCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_QueryPairs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_QueryPairs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PreparedQueryEffectsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PreparedQueryEffectsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QuerySamplerOutput.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QuerySamplerOutput"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QueryAddress.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QueryAddress"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_OpeningJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_OpeningJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_OpeningCalls.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_OpeningCalls"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_WideEncoding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_WideEncoding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PreparedQueryErasureV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PreparedQueryErasureV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
