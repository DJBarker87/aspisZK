import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireRawFullPublicSelection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireRawFullPublicSelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireRawLiteralRecordedDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireRawLiteralRecordedDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawCompiledChecksOriginalScheduleBin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawCompiledChecksOriginalScheduleBin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawRecordedPublicSpendExtractorPublicEqualityBin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawRecordedPublicSpendExtractorPublicEqualityBin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/LiteralCheckedByteSpendExtractor.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "LiteralCheckedByteSpendExtractor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawEnrichedOpeningWordIdentity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawEnrichedOpeningWordIdentity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_PrepareBuffers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_PrepareBuffers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_VerifyLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_VerifyLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_TraceUnique.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_TraceUnique"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_InitUnique.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_InitUnique"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_CodeBind.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_CodeBind"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_LevelsBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_LevelsBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_CountTactic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_CountTactic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawK_ChildHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawK_ChildHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawK_TraceLogs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawK_TraceLogs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port9OR_BatchStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port9OR_BatchStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Begin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Begin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_SemanticFinish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_SemanticFinish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_RehashPublic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_RehashPublic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_TranscriptNew.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_TranscriptNew"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Scalar.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Scalar"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Rho.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Rho"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Queries.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Queries"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_ClaimDictionary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_ClaimDictionary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R16CanonReduction.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R16CanonReduction"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireRawAdaptiveCompiledCompletion.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireRawAdaptiveCompiledCompletion"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireInitialTag.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireInitialTag"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeRef/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeRef.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/BinHonestStartFrames.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "BinHonestStartFrames"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/BinRawByteCutRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "BinRawByteCutRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/BinMerkleLogExtension.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "BinMerkleLogExtension"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Batches.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Batches"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_LifetimeVersion.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_LifetimeVersion"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideMulCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideMulCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideQMField.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideQMField"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_NativeAction.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_NativeAction"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_Association.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_Association"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_AccountAccepted.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_AccountAccepted"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_ScheduleLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_ScheduleLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_BudgetLaws.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_BudgetLaws"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_QueryTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_QueryTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_FoldedData.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_FoldedData"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_DomainLanes.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_DomainLanes"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_LineModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_LineModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/BoundedSamplerWrapper.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.BoundedSamplerWrapper"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R15/CircleChord.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R15.CircleChord"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FinalResponses.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FinalResponses"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FirstFold.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FirstFold"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ParentSupport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ParentSupport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FoldCoefficientBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FoldCoefficientBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/EncoderLinearity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.EncoderLinearity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1JointList.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1JointList"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/Initial.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.Initial"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/V3/DQChain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.V3.DQChain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ParsedStateTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ParsedStateTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CarryLast.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CarryLast"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Data/Array/Lemmas.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Data.Array.Lemmas"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Raw/Ops.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.Raw.Ops"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Linear.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.Linear"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTT/Evaluation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTT.Evaluation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTT/Forward.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTT.Forward"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTT/Inverse.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTT.Inverse"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTT/Kernel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTT.Kernel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Raw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.Raw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTTFast/Correctness/Pair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTTFast.Correctness.Pair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTTFast/Correctness/Radix4DIT.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTTFast.Correctness.Radix4DIT"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPolyFactorMeanTools.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPolyFactorMeanTools"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawByteCutRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawByteCutRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawLiteralRecordedDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawLiteralRecordedDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawLiteralCompiledDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawLiteralCompiledDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawRecordedPublicSpendExtractorPublicEquality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawRecordedPublicSpendExtractorPublicEquality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/LiteralFreshAttemptBound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "LiteralFreshAttemptBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSRejectingSamplerDecoderBank.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSRejectingSamplerDecoderBank"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31PairedSamplerMass.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31PairedSamplerMass"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31PairedSamplerRejectBound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31PairedSamplerRejectBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawAdaptiveClassifierHitDensity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawAdaptiveClassifierHitDensity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/FinalEncoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.FinalEncoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralOpeningDataRows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralOpeningDataRows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CandidateBaseProjection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CandidateBaseProjection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ConcreteSpendExtraction.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ConcreteSpendExtraction"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SemanticCandidateList.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SemanticCandidateList"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SemanticHit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SemanticHit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/MaskEarly.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.MaskEarly"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralOpeningBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralOpeningBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralIndexedPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralIndexedPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralQueryBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralQueryBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralRhoBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralRhoBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralQueryCurrentRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralQueryCurrentRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralQueryContext.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralQueryContext"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SemanticOpening.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SemanticOpening"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SemanticTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SemanticTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SelectedCircleWeightModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SelectedCircleWeightModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/MaskProtocol.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.MaskProtocol"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1AdapterReconstruct/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1AdapterReconstruct.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1AdapterReconstruct/FunsExternal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1AdapterReconstruct.FunsExternal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PublicSerializerWhole431.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PublicSerializerWhole431"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PublicRawCore.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PublicRawCore"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1WithdrawalValidation/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1WithdrawalValidation.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PublicSourceRawMap.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PublicSourceRawMap"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalCutOpening.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalCutOpening"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
