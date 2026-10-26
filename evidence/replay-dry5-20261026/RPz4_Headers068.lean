import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPG_Game.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPG_Game"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_CompleteInstall.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_CompleteInstall"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_BankSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_BankSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_Persistence.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_Persistence"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPH_Extract.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPH_Extract"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc2_Top.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc2_Top"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_ReaderEntry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_ReaderEntry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_RuntimeBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_RuntimeBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_KeyLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_KeyLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_CommittedPayload.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_CommittedPayload"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_SecondSnapshot.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_SecondSnapshot"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_DecodedShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_DecodedShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_AtomicLaws.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_AtomicLaws"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_Persistence.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_Persistence"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_BankBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_BankBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_CollisionBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_CollisionBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_FirstPrepare.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_FirstPrepare"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_EntryPrivileges.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_EntryPrivileges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_InstalledRecovered.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_InstalledRecovered"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_DataBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_DataBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_OnRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_OnRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/EndP_Headline.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EndP_Headline"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_Implementation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_Implementation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_PairProgram.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_PairProgram"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_Finish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_Finish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_NativePair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_NativePair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_PublicCarrier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_PublicCarrier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Par_Parameters.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Par_Parameters"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FinT_Pairing.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinT_Pairing"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FinT_Returned.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinT_Returned"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4D_ReturnedFinish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4D_ReturnedFinish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RowFinish_Finalization.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RowFinish_Finalization"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_PrepareRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_PrepareRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkC_Replay.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkC_Replay"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_CodeIf.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_CodeIf"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_ResumePrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_ResumePrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_TailJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_TailJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_Silent.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_Silent"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4D_FinishInstall.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4D_FinishInstall"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_WriterCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_WriterCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytesSparseDigest.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytesSparseDigest"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_WriterRoot1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_WriterRoot1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_WriterSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_WriterSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_Reader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_Reader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_NativeInstance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_NativeInstance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_OriginalEndpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_OriginalEndpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_Domain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_Domain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2I_Accepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2I_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_Execution.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_Execution"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_Decode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_Decode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RowOrder_History.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RowOrder_History"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op3I_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op3I_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2I_Finish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2I_Finish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op3I_Accepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op3I_Accepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_D189Consolidation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_D189Consolidation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Final.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Final"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-op4-p6-20261025/Op4P_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op4P_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_Child.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_Child"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Uni_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Uni_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_SuccessAccepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_SuccessAccepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_SamePair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_SamePair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_SelectedPaths.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_SelectedPaths"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Tx2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Tx2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_SafResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_SafResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Deployed.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Deployed"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_ChargedBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_ChargedBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_NativeConsolidation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_NativeConsolidation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_ByteSelection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_ByteSelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_AccountAudit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_AccountAudit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AdapterRwAccepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AdapterRwAccepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAF_PreparedCont.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAF_PreparedCont"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAF_LiteralCaller.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAF_LiteralCaller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_LiteralCaller.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_LiteralCaller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc5_Literal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc5_Literal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_SameCut.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_SameCut"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Execution.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Execution"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/RawTx1DigestLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawTx1DigestLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkC_Source.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkC_Source"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_PreparePort.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_PreparePort"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_InputDiscovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_InputDiscovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SamplerAligned.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SamplerAligned"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_OrdinaryReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_OrdinaryReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_DataRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_DataRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_SourceCuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_SourceCuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedPrefixTypedFull.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixTypedFull"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_OpeningLateEntries.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_OpeningLateEntries"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_TypedFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_TypedFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_SamplerStatement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_SamplerStatement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_OpeningFirst4.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_OpeningFirst4"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_SamplerIndex.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_SamplerIndex"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_SourceQueryDecode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_SourceQueryDecode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_OpeningCalls.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_OpeningCalls"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_OpeningPayloads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_OpeningPayloads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_OpeningStages.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_OpeningStages"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_OpeningLast2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_OpeningLast2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_SamplerOne.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_SamplerOne"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_SourceRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_SourceRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_RunState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_RunState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_PrefixWitness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_PrefixWitness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
