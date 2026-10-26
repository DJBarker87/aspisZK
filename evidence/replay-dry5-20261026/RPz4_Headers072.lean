import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3W_SourceLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3W_SourceLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_FirstHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_FirstHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_OracleHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_OracleHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_SemanticBytes.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_SemanticBytes"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_HeadCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_HeadCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_FinishLeaves.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_FinishLeaves"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_ModelAcceptance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_ModelAcceptance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_AcceptanceValues.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_AcceptanceValues"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_RunEvidence.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_RunEvidence"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_Trace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_Trace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Ten.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Ten"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_WriterModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_WriterModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_TenInput.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_TenInput"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_Pointwise.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_Pointwise"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_Joint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_Joint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Probability.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Probability"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_ByteTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_ByteTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_Projection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_Projection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_EvidenceCalls.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_EvidenceCalls"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_RehashValue.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_RehashValue"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_CheckpointBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_CheckpointBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_BatchBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_BatchBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_Experiment.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_Experiment"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_FirstPairLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_FirstPairLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_FirstCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_FirstCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_FirstCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_FirstCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/V3/Gen.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.V3.Gen"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/OracleFiniteSupport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.OracleFiniteSupport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Prefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Prefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Bounds.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Bounds"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortStoredAdmissionC4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortStoredAdmissionC4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/OracleProgramOps.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.OracleProgramOps"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Charged.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Charged"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3_Model.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3_Model"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_RowBounds.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_RowBounds"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_Physical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_Physical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_SelectedAccepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_SelectedAccepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port1_DriverSubstitution.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port1_DriverSubstitution"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeSemanticRows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeSemanticRows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OracleDecisionPrereqPaths.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OracleDecisionPrereqPaths"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/BinPerQueryNumeric.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "BinPerQueryNumeric"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_DirectPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_DirectPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_LiteralConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_LiteralConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_LiteralResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_LiteralResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_ClosedPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_ClosedPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_DirectConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_DirectConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_DirectResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_DirectResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_ActualPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_ActualPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_CloseConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_CloseConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_ClosedResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_ClosedResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_PairSelected.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_PairSelected"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_ActualResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_ActualResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_SourceConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_SourceConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_ResultSelected.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_ResultSelected"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_DirectOutcome.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_DirectOutcome"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_FinishSaved.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_FinishSaved"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ClosedOutcome.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ClosedOutcome"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_DirectCaller.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_DirectCaller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_SourceOutcome.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_SourceOutcome"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ClosedCaller.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ClosedCaller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ActualCaller.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ActualCaller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_FinishEffects.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_FinishEffects"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_PreparedOutcome.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_PreparedOutcome"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_LiteralCont.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_LiteralCont"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_EntryFlags.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_EntryFlags"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_BankSourceLoad.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_BankSourceLoad"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_PhysicalKey.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_PhysicalKey"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_AtomicRecordNative.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_AtomicRecordNative"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_BankFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_BankFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_RecordDecode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_RecordDecode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_LineQuery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_LineQuery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_Compatibility.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_Compatibility"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_StepProtection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_StepProtection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_ReaderMarker.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_ReaderMarker"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_Asq8Guards.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_Asq8Guards"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_ValidateCut.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_ValidateCut"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_Metadata.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_Metadata"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_RuntimeEntry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_RuntimeEntry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_TwoFieldAudit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_TwoFieldAudit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_D189Interpretation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_D189Interpretation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_ReturnedCheckpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_ReturnedCheckpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_SnapshotJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_SnapshotJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_SdkShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_SdkShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_ProvenanceModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_ProvenanceModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_ProgramErasure.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_ProgramErasure"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_ScheduleSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_ScheduleSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_Classify.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_Classify"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_InstalledBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_InstalledBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_OraclePort.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_OraclePort"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_BatchDictionary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_BatchDictionary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AdapterRwModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AdapterRwModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_AcceptedTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_AcceptedTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_ReplayPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_ReplayPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/EndP_Collision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EndP_Collision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_Installation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_Installation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_FirstAccepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_FirstAccepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port8EFF_NativeReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port8EFF_NativeReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_FirstHeadBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_FirstHeadBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
