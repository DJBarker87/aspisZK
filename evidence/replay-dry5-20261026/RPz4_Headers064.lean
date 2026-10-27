import Lean
open Lean Elab Command
run_cmd do
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc7_Native.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc7_Native"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Release.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Release"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Accounting.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Accounting"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_Cost.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_Cost"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc6_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc6_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P6C_Extension.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6C_Extension"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_InstalledLaws.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_InstalledLaws"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_Bound.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_Bound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_SourceClaims.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_SourceClaims"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_AccountMass.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_AccountMass"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_ModelClaims.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_ModelClaims"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_Range.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_Range"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Source.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Source"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Close.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Close"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Install.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Recorder.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Recorder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Trace.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Trace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Program.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Program"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Pair.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Pair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Protection.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Protection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc2_Events.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc2_Events"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPG_Pair.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPG_Pair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPG_Account.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPG_Account"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_Install.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_ConditionalClaims.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_ConditionalClaims"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPG_History.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPG_History"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_PhysicalResult.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_PhysicalResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_NativePair.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_NativePair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Accepted.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_SourceHeadline.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_SourceHeadline"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Pair.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Pair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Finish.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Finish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Native.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Native"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Continuation.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Continuation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Base.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Base"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Caller.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Caller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Result.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_FullResult.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_FullResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2R_Pair.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2R_Pair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Par_Headline.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Par_Headline"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Par_Transcript.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Par_Transcript"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_NativeBuild.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_NativeBuild"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_FinishProof.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_FinishProof"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Cons_Second.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Cons_Second"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_ReaderEffects.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_ReaderEffects"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPhy_Physical.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPhy_Physical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_FinishResult.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_FinishResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPhy_Header.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPhy_Header"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPhy_Ranges.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPhy_Ranges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPhy_Accepted.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPhy_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_NativeEndpoint.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_NativeEndpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_Accepted.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_Inner.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_Inner"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_Uni.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_Uni"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  logInfo "RPZ4_HEADERS_COMPLETE"
