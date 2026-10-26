import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_OracleSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_OracleSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_TraceProtection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_TraceProtection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_InstalledReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_InstalledReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_ReaderAuthority.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_ReaderAuthority"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_CausalBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_CausalBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_D189Wrappers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_D189Wrappers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_DigestExtraction.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_DigestExtraction"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_D189Entry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_D189Entry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_DrvShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_DrvShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_Atomic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_Atomic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_BankState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_BankState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_BankEvents.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_BankEvents"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_AccountBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_AccountBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_CurrentSlots.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_CurrentSlots"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_MapCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_MapCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AdapterRwCuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AdapterRwCuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Recovered.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Recovered"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Pair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Pair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Context.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Context"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/EndP_Endpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EndP_Endpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/EndP_AuthMass.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EndP_AuthMass"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_Dictionary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_Dictionary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_RetainedReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_RetainedReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_FirstProgram.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_FirstProgram"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_SecondProgram.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_SecondProgram"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_Twelve.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_Twelve"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SelectedTranscriptParams.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SelectedTranscriptParams"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FinalSoundness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FinalSoundness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FinT_Comparisons.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinT_Comparisons"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FinT_Algebra.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinT_Algebra"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4D_FinishFrozen.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4D_FinishFrozen"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4D_Pairing.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4D_Pairing"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortFrozen2Checkpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozen2Checkpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4D_FlushRows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4D_FlushRows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S8Kani2CallerJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S8Kani2CallerJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_ClosedRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_ClosedRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_RootSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_RootSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AuS1_Observe.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AuS1_Observe"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkC_GlobalRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkC_GlobalRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozen2Bounds.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozen2Bounds"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_CodeEq.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_CodeEq"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_ResultEq.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_ResultEq"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4A_NativeReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4A_NativeReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_TailFactor.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_TailFactor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytes5Effect.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytes5Effect"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4D_Round.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4D_Round"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4D_Value.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4D_Value"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_Parents.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_Parents"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_FirstPaths.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_FirstPaths"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytesBodyArithmetic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytesBodyArithmetic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytesDigest.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytesDigest"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_Install.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytes5Join.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytes5Join"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeEndian.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeEndian"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_FissionedRoot.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_FissionedRoot"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_FissionedFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_FissionedFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_SourceWriter.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_SourceWriter"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_Endpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_Endpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_Arithmetic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_Arithmetic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q2-20261024/Port5Q2_Prepared.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q2_Prepared"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2I_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2I_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_GeometryReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_GeometryReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx2N_DecodeHeader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx2N_DecodeHeader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op3I_Install.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op3I_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_ScheduledConsolidation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_ScheduledConsolidation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-op4-p6-20261025/Op4P_Install.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op4P_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_FirstChild.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_FirstChild"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_Second.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_Second"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_NativeAuth.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_NativeAuth"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozenOrderSelectedRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozenOrderSelectedRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Op3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Op3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_R3Result.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_R3Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_FinalTop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_FinalTop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_AuditQueries.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_AuditQueries"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_AuthenticatedInputs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_AuthenticatedInputs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_AccountExperiment.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_AccountExperiment"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_JointCharge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_JointCharge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AdapterRwConstants.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AdapterRwConstants"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AdapterRwRanges.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AdapterRwRanges"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAF_PreparedOutcome.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAF_PreparedOutcome"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAF_LiteralCont.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAF_LiteralCont"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_LiteralCont.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_LiteralCont"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAF_FinishPrepared.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAF_FinishPrepared"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc4_Model.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc4_Model"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_LiteralFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_LiteralFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_NumericTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_NumericTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_SaveOnRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_SaveOnRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Attach.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Attach"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_FinishParsed.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_FinishParsed"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_InputQuery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_InputQuery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Discovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Discovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_PreparedSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_PreparedSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Immutable.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Immutable"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_SameDigest.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_SameDigest"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Rebind.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Rebind"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/RawSourceGlobalOracleInitial.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawSourceGlobalOracleInitial"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_OpeningDataFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_OpeningDataFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_OpeningInputLate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_OpeningInputLate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
