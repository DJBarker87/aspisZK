import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_SamplerCompose.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_SamplerCompose"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_CirclePair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_CirclePair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_SamplerStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_SamplerStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_First25.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_First25"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_InitialValue.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_InitialValue"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_SemanticPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_SemanticPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_CurrentPhysical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_CurrentPhysical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_BothBuffers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_BothBuffers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_Values.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Values"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-sem-20261025/PSem_Root.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Root"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-sem-20261025/PSem_SemanticTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_SemanticTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P6C_Whole.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6C_Whole"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P6C_Callbacks.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6C_Callbacks"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_CutAcceptance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_CutAcceptance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/TxS_Writer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "TxS_Writer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/TxS_RawTen.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "TxS_RawTen"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_CanonicalCarrier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_CanonicalCarrier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3L_RhoCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3L_RhoCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_SampleCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_SampleCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_SemanticSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_SemanticSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_CircleCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_CircleCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_CircleCalls.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_CircleCalls"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_AlphaTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_AlphaTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_CoordinateTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_CoordinateTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_LiteralCont.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_LiteralCont"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/NP6_RecordShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "NP6_RecordShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Control.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Control"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Nonvacuity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Nonvacuity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_Strict.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Strict"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Model.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Model"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/EndP_Numeric.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EndP_Numeric"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_CollisionJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_CollisionJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_Join.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_Join"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkC_SourceLaws.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkC_SourceLaws"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5T_Install.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5T_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_Install.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozenOrderRecoveryLevels.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozenOrderRecoveryLevels"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozenOrderLeaves.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozenOrderLeaves"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op5I_EventCounterexample.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op5I_EventCounterexample"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_CircleSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_CircleSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_CircleScope.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_CircleScope"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_Domain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_Domain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_Inverse.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_Inverse"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_AllWorldInput.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_AllWorldInput"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/NP6_StdModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "NP6_StdModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_Aligned.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_Aligned"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3W_SourceHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3W_SourceHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_CanonicalNative.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_CanonicalNative"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/FGl_Leaves.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FGl_Leaves"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_ModelAcceptance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_ModelAcceptance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_AllWorldRuns.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_AllWorldRuns"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_CollisionErase.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_CollisionErase"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Checkpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Checkpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_RuntimePointwise.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_RuntimePointwise"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_Averaging.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_Averaging"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_ModelClaims.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_ModelClaims"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Runtime.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Runtime"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_Account.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_Account"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_SourcePrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_SourcePrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3X_Preparation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3X_Preparation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_FirstBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_FirstBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_SecondBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_SecondBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_GlobalBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_GlobalBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3W_FirstLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3W_FirstLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1AllAddressFiatShamir.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1AllAddressFiatShamir"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Causal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Causal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Canon.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Canon"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortPureOutputC7.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortPureOutputC7"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_TwoPass.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_TwoPass"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_InputRows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_InputRows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-align-20261026/PAln_Public.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PAln_Public"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port1_StoredCarrier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port1_StoredCarrier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OracleDecisionPrereqNumeric.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OracleDecisionPrereqNumeric"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_LiteralFull.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_LiteralFull"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_C_SAP_LiteralPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_C_SAP_LiteralPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_AcceptedValue.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_AcceptedValue"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_DirectPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_DirectPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_LiteralConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_LiteralConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_LiteralResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_LiteralResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ClosedPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ClosedPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_DirectConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_DirectConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_DirectResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_DirectResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ActualPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ActualPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_CloseConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_CloseConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ClosedResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ClosedResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_PairSelected.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_PairSelected"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ActualResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ActualResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_SourceConsumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_SourceConsumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_NativePair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_NativePair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_ResultSelected.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_ResultSelected"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_PreparedCont.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_PreparedCont"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAF_LiteralCaller.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAF_LiteralCaller"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_BoundaryLoad.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_BoundaryLoad"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_Ordinary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_Ordinary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPS_ParentStatus.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPS_ParentStatus"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPR_DataPersistence.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPR_DataPersistence"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/CPP_BankHistory.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CPP_BankHistory"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_Decoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_Decoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
