import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SourceAlphaIndex.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SourceAlphaIndex"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_QueryPorts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_QueryPorts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortStoredDecisionDraftC4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortStoredDecisionDraftC4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_AlignedPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_AlignedPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SamplerMessages.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SamplerMessages"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SamplerOrdinary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SamplerOrdinary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SamplerAt.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SamplerAt"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_EraseIndex.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_EraseIndex"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_RestoreChallenge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_RestoreChallenge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_LiteralPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_LiteralPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_RowKappa.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_RowKappa"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_RowFirst.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_RowFirst"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_RowLast.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_RowLast"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1NativePrepareBuffersV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1NativePrepareBuffersV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedPrefixRowPayload.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixRowPayload"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SemanticPrefixCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SemanticPrefixCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_RhoEntry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_RhoEntry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QueryOne.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QueryOne"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_LateFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_LateFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_OpeningPair27.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_OpeningPair27"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_OpeningPair29.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_OpeningPair29"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_SamplerProtocol.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_SamplerProtocol"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_ConcreteDecode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_ConcreteDecode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QueryDecoderSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QueryDecoderSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralQuerySample.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralQuerySample"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_QueryFull.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_QueryFull"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_RhoJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_RhoJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_PayloadFits.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_PayloadFits"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_InactivePhysical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_InactivePhysical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ClosedPreparationHashCodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ClosedPreparationHashCodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_LengthFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_LengthFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_OpeningReach.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_OpeningReach"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_RhoOne.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_RhoOne"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_SamplerStructure.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_SamplerStructure"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_SamplerRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_SamplerRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_CircleJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_CircleJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_InitialLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_InitialLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_SemanticValue.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_SemanticValue"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_RowBindings.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_RowBindings"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_Row30Source.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_Row30Source"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_FullCut.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_FullCut"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PrepareBothBuffersV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PrepareBothBuffersV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1WideViewY1V1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1WideViewY1V1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_Expand.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Expand"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ValuesOwnedAcceptedBytesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ValuesOwnedAcceptedBytesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-sem-20261025/PSem_RoundCalls.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_RoundCalls"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedSourceFull25Frames.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedSourceFull25Frames"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticFinishBoundsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticFinishBoundsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P6C_OnCuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6C_OnCuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_FirstPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_FirstPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_SecondPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_SecondPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port9OR_P6Node.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port9OR_P6Node"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_LeafCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_LeafCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_DecodeCut.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_DecodeCut"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_WriterReturned.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_WriterReturned"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_Borrowed.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_Borrowed"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_InactiveCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_InactiveCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPreparedInstalledMeaning.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPreparedInstalledMeaning"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SourceNumeric.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SourceNumeric"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_FlushInstall.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_FlushInstall"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_CircleSourceCall.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_CircleSourceCall"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_WrapperCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_WrapperCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticFinishModelV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticFinishModelV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedDigest32Callers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedDigest32Callers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_LiteralOutcome.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_LiteralOutcome"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/NP6_ClaimsRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "NP6_ClaimsRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedPrefixParse.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixParse"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Initial.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Initial"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Accepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-op4-p6-20261025/Op4P_Audit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op4P_Audit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_Validation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Validation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_Canonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Canonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Uni_CanonicalPerAttempt.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Uni_CanonicalPerAttempt"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Bound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Bound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_CanonicalJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_CanonicalJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_Canonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_Canonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalLevels.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalLevels"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/SqueezeOracleBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.SqueezeOracleBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_BatchStd.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_BatchStd"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_KeyInstall.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_KeyInstall"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozenOrderRecoveryStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozenOrderRecoveryStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortFrozenOrderDecision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozenOrderDecision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SInt2_AcceptedPairClaims.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SInt2_AcceptedPairClaims"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_RhoMeaning.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_RhoMeaning"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/R4TransportCircleCoordinates.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R4TransportCircleCoordinates"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_Geometry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_Geometry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_InverseExecution.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_InverseExecution"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_InverseFieldModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_InverseFieldModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_FirstRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_FirstRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_SourceInput.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_SourceInput"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_IdealBackend.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_IdealBackend"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Parser.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Parser"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ClaimsUnrolledFinish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ClaimsUnrolledFinish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_RunFinish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_RunFinish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_ReadModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_ReadModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_PreparedAt.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_PreparedAt"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3W_LogJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3W_LogJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_ReadModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_ReadModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_ModelAcceptance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_ModelAcceptance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_AcceptanceValues.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_AcceptanceValues"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
