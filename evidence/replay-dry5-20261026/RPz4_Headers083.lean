import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_ModelBody.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_ModelBody"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_AuthenticatedTen.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_AuthenticatedTen"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_SameRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_SameRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_RecordCuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_RecordCuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_EffectLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_EffectLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_ReaderSyntax.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_ReaderSyntax"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R9PoolRuntimeBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R9PoolRuntimeBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_StageDictionary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_StageDictionary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_StageBatch.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_StageBatch"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_CodeTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_CodeTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawK_PrepareHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawK_PrepareHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_LowerTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_LowerTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_MapSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_MapSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_SemanticHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_SemanticHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_Result.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_Result"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_InitFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_InitFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_AcceptedParser.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_AcceptedParser"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_FinishWitness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_FinishWitness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_EventExtension.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_EventExtension"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_FirstBatchModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_FirstBatchModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_SecondModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_SecondModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_FirstModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_FirstModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_CheckedView.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_CheckedView"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCleanModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCleanModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Tag.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Tag"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortPool.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortPool"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OracleDecisionMultiNumeric.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OracleDecisionMultiNumeric"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawRecordedActualAdaptiveFailureBoundBin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawRecordedActualAdaptiveFailureBoundBin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawExtractorCostComposedBin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawExtractorCostComposedBin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_PreparedExact.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_PreparedExact"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_PreparedSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_PreparedSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_Admission.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_Admission"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PreparedOracleCodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PreparedOracleCodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_BatchLoopBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_BatchLoopBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_BatchCredit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_BatchCredit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_SdkDictionary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_SdkDictionary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_NativeChildren.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_NativeChildren"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_BatchLoop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_BatchLoop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port9OR_BatchTree.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port9OR_BatchTree"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Preparation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Preparation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS2/LemmaA.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS2.LemmaA"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS/LemmaB.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS.LemmaB"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OracleDecisionMultiAccounting.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OracleDecisionMultiAccounting"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCanon.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCanon"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/D0InstanceAdmission.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "D0InstanceAdmission"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/InitialTagDecision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "InitialTagDecision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R3SemanticRemainingJoins.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R3SemanticRemainingJoins"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortReplay.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortReplay"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_Arithmetic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_Arithmetic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port1_LibrarySource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port1_LibrarySource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/VTop_OracleStages.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "VTop_OracleStages"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeRowEncoding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeRowEncoding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeExpansionLength.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeExpansionLength"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeRowShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeRowShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeFrameHeader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeFrameHeader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeHeader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeHeader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeVecLaws.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeVecLaws"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OracleDecisionFeasibilityCore.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OracleDecisionFeasibilityCore"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R19BudgetOriginalReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R19BudgetOriginalReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/BinThreeCommitmentTypedOpening.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "BinThreeCommitmentTypedOpening"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_SdkAccepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_SdkAccepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PoolT_CopyShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PoolT_CopyShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_RecordNative.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_RecordNative"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_AtomicOrigin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_AtomicOrigin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_AtomicTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_AtomicTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_TraceAppend.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_TraceAppend"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1RecordParser/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1RecordParser.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedRecordLimbCanonicality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedRecordLimbCanonicality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideMulExactProduct.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideMulExactProduct"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_LineAlgebra.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_LineAlgebra"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_LineCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_LineCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_RawWide.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_RawWide"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_LineEmbedding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_LineEmbedding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ZCircleFoldMathV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ZCircleFoldMathV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_Call.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_Call"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_EntryZero.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_EntryZero"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_ZeroReject.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_ZeroReject"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_CallBirth.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_CallBirth"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_SiteSchedule.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_SiteSchedule"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2W_WrapperLaws.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2W_WrapperLaws"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AdapterRwRuntimeAdmission.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AdapterRwRuntimeAdmission"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hist_SourceMarker.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hist_SourceMarker"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_Factory.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_Factory"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_Second.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_Second"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_OuterHelpers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_OuterHelpers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_FirstBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_FirstBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_SecondBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_SecondBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_OuterBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_OuterBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_ChildCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_ChildCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_OuterGoodStage1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_OuterGoodStage1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_OuterGoodStage2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_OuterGoodStage2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_RecordTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_RecordTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_CallCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_CallCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_SecondCut.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_SecondCut"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvI_Installation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvI_Installation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_NodeBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_NodeBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_FirstLibrary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_FirstLibrary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_Observation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_Observation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_QueryState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_QueryState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
