import Lean
open Lean Elab Command
run_cmd do
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_R5Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_R5Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_R5Close.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_R5Close"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Source.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Source"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_R6Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_R6Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_NativeSelection.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_NativeSelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Charge.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Charge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Origin.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Origin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc6_Caller.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc6_Caller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-final-20261026/PFin_Packet.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PFin_Packet"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P6C_FullBoundary.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6C_FullBoundary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_Acceptance.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_Acceptance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc4_Encoding.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc4_Encoding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_PrepareOwner.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_PrepareOwner"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc3_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc3_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Caller.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Caller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/TxS_RawPublic.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "TxS_RawPublic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Nonvacuity.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Nonvacuity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc2_Base.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc2_Base"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_Parser.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_Parser"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_Acceptance.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_Acceptance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_Ten.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_Ten"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_Finish.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_Finish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_ContSource.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_ContSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_CallerSource.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_CallerSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_PublicDecode.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_PublicDecode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_AccountCharge.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_AccountCharge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_CollisionLaw.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_CollisionLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_SourceCost.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_SourceCost"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P6C_Accepted.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6C_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_P6.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_P6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Binding.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Binding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_Constructor.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_Constructor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_Installation.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_Installation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_Join.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_Join"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_JointCongr.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_JointCongr"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_ConditionalBound.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_ConditionalBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_Cost.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_Cost"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_AccountReads.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_AccountReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3W_CollisionFree.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3W_CollisionFree"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Cost.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Cost"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_ByteCarrier.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_ByteCarrier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_Margin.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_Margin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_RangeEdges.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_RangeEdges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_RangeChord.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_RangeChord"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Extract.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Extract"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAF_FinalTop.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAF_FinalTop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc3_Install.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc3_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_LiteralTop.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_LiteralTop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_FinalResult.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_FinalResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_Top.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_Top"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc3_Top.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc3_Top"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc2_Protection.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc2_Protection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PoolT_Write.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PoolT_Write"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAF_FinalResult.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAF_FinalResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc2_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc2_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Game.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Game"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Install.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPG_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPG_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc4_Install.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc4_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_BankRecorder.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_BankRecorder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_Nonvacuity.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_Nonvacuity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Rc2Source.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Rc2Source"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Close.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Close"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPG_Accepted.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPG_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_SourceBank.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_SourceBank"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_FirstShape.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_FirstShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_SourceTop.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_SourceTop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_AtomicSource.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_AtomicSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_AtomicBank.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_AtomicBank"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_AccountSource.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_AccountSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_ConditionalSum.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_ConditionalSum"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_FirstConstants.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_FirstConstants"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_Authority.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_Authority"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_SourceCost.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_SourceCost"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Conditional.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Conditional"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_DataWriter.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_DataWriter"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_CallerSource.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_CallerSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_Accepted.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Install.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Map.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Map"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_Headline.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_Headline"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_SourceEntry.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_SourceEntry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Ten.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Ten"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Finish.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Finish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_ResultSource.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_ResultSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Par_NativePair.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Par_NativePair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Par_Public.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Par_Public"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FinT_Model.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinT_Model"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Recovery.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Recovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_ResumeCode.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_ResumeCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_ReaderJoin.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_ReaderJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_FinishCode.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_FinishCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RowFinish_Control.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RowFinish_Control"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPhy_HeaderCells.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPhy_HeaderCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_WriterRoots.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_WriterRoots"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_Header.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_Header"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeSlices.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeSlices"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  logInfo "RPZ4_HEADERS_COMPLETE"
