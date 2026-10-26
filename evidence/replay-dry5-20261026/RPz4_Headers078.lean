import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PreparedSourceEffectsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PreparedSourceEffectsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1PreparedActiveBoundariesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1PreparedActiveBoundariesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_OpeningFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_OpeningFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_BlockCodeValue.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_BlockCodeValue"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1SemanticCodeCircleValidatedV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticCodeCircleValidatedV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_BlockCalls.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_BlockCalls"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_ReseedSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_ReseedSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentCompactCallerModelV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentCompactCallerModelV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ValuesOwnedReferenceBytesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ValuesOwnedReferenceBytesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ValuesOwnedInstallationV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ValuesOwnedInstallationV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ValuesOwnedOuterTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ValuesOwnedOuterTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1PublicPreparation/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1PublicPreparation.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P6C_Pair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P6C_Pair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_BatchFixed.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_BatchFixed"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkC_BatchSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkC_BatchSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_SecondCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_SecondCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port9OR_Reply.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port9OR_Reply"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_TailReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_TailReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_CallerViews.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_CallerViews"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeByteEquality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeByteEquality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytes5Trace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytes5Trace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WireTx2Records.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WireTx2Records"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawDigestLogCarrier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawDigestLogCarrier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_Bytes.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_Bytes"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbiTry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbiTry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPreparedScratchModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPreparedScratchModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/SelectedWideViewFunsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SelectedWideViewFunsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PreparedParsedInactiveV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PreparedParsedInactiveV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PreparedFromQmSourceBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PreparedFromQmSourceBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPreparedConcreteQueryRho.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPreparedConcreteQueryRho"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPreparedCandidateSamplers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPreparedCandidateSamplers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3K_PreparedSourceFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3K_PreparedSourceFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_FirstCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_FirstCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_QueryFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_QueryFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_Constructor.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_Constructor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S8JoinFinishExact.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S8JoinFinishExact"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedCurrentQM31Exact.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedCurrentQM31Exact"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1SemanticPhaseV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticPhaseV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedPrefixParseCore.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixParseCore"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/NP6_ClaimsSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "NP6_ClaimsSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedPrefixRecordStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixRecordStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Tx1Q_Install.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Tx1Q_Install"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_Ten.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_Ten"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q2-20261024/Port5Q2_Checkpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q2_Checkpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Op3I_Nonvacuity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Op3I_Nonvacuity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_RecordChain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_RecordChain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_Lengths.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Lengths"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedPrefixStrictPayload.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixStrictPayload"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_PreparedAt.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_PreparedAt"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalDigest.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalDigest"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeOrderedLevel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeOrderedLevel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR72Sampler/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR72Sampler.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/DuplexFrames.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.DuplexFrames"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/DuplexFreshPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.DuplexFreshPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_NativeBatchBody.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_NativeBatchBody"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_TreeJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_TreeJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortBatchDraft.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortBatchDraft"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortShortCircuitCore.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortShortCircuitCore"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortJoinSplitDecision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortJoinSplitDecision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SInt2_S1SdkSelectedSemanticTraceV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SInt2_S1SdkSelectedSemanticTraceV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ClaimsUnrolledVerify.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ClaimsUnrolledVerify"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedDigest32SamplerTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedDigest32SamplerTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/SemD2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.SemD2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_Geometry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_Geometry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17CurrentDomainSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17CurrentDomainSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S7JoinBasisMachine.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S7JoinBasisMachine"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_SquareSourceModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_SquareSourceModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Public.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Public"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1SemanticCurrentCodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticCurrentCodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_AllWorldPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_AllWorldPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_Tx1Run.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_Tx1Run"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_FoldedCut.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_FoldedCut"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ClaimsUnrolledParentSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ClaimsUnrolledParentSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1SemanticCallExtraction/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1SemanticCallExtraction.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1DecodeKFullV10/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1DecodeKFullV10.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_FinishSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_FinishSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Y_delivered/F3Y_PreparedScalars.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Y_PreparedScalars"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_SecondOnRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_SecondOnRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_SecondCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_SecondCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3W_FirstBatch.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3W_FirstBatch"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_WriterCall.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_WriterCall"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_SecondBatch.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_SecondBatch"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_CheckpointStage.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_CheckpointStage"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_Variant.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_Variant"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_CheckpointLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_CheckpointLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_PairModelFinish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_PairModelFinish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_CheckpointSplice.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_CheckpointSplice"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2X_RuntimeRetention.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2X_RuntimeRetention"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_FinishProof.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_FinishProof"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3_Checkpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3_Checkpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_RoundValues.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_RoundValues"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_ReifyLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_ReifyLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_PairInputs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_PairInputs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_SecondCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_SecondCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawK_CodeHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawK_CodeHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_PrepareHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_PrepareHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_FirstTailCode.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_FirstTailCode"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_SdkPure.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_SdkPure"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_Try.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_Try"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RowOrder_FrozenSchedule.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RowOrder_FrozenSchedule"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
