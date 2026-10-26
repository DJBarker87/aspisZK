import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_Padding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_Padding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeP6Frozen2Stage.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeP6Frozen2Stage"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S8JoinFrozenScan.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S8JoinFrozenScan"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Stage2ContinuationResume.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Stage2ContinuationResume"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/UnrolledWideByteReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "UnrolledWideByteReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnrolledWideLimbChecks.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnrolledWideLimbChecks"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CandidateWideParserContracts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CandidateWideParserContracts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PreparedSourcePowersJointRankV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PreparedSourcePowersJointRankV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisC2HostEmbedding/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisC2HostEmbedding.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31ConcreteMaterializedSchedule.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31ConcreteMaterializedSchedule"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Query31MathematicalSchedule.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Query31MathematicalSchedule"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPreparedGammaSpecialization.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPreparedGammaSpecialization"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentSamplerPreparedCarrierBoundsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentSamplerPreparedCarrierBoundsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPreparedOriginalPayload.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPreparedOriginalPayload"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPreparedConcreteRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPreparedConcreteRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimPowerReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimPowerReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_InstalledPrepare.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_InstalledPrepare"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1CurrentPrepareBudgetV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1CurrentPrepareBudgetV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port2_QueryAdvance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port2_QueryAdvance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port2_ReturnedState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port2_ReturnedState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_Constants.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_Constants"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedCurrentQM31Mul.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedCurrentQM31Mul"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R17/QM31WordTower.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R17.QM31WordTower"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentCompactTx1ReachabilityV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentCompactTx1ReachabilityV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6DecoderScopedReuseV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6DecoderScopedReuseV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1PrefixAggregateParser/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1PrefixAggregateParser.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q2-20261024/Port5Q2_Ten.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q2_Ten"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/PSem_Loop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PSem_Loop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/ExtractedRecordValidator.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedRecordValidator"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeLiveReference.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeLiveReference"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeLiveBatch.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeLiveBatch"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8Privacy/FiniteGames.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8Privacy.FiniteGames"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_Prepared.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_Prepared"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_TailRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_TailRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OracleDecisionMultiRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OracleDecisionMultiRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortRuntimeBindingC7.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortRuntimeBindingC7"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1AcceptedChallengesNumericV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1AcceptedChallengesNumericV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1NativeBufferPreparedTraceV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1NativeBufferPreparedTraceV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SInt2_S6SdkOriginalObjectCallerV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SInt2_S6SdkOriginalObjectCallerV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SInt2_S6SdkSelectedSemanticCutV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SInt2_S6SdkSelectedSemanticCutV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SInt2_S6SdkStage1ReuseFactoredV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SInt2_S6SdkStage1ReuseFactoredV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SInt2_S6SdkSourceCutReuseV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SInt2_S6SdkSourceCutReuseV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1OwnedStage1NumericV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1OwnedStage1NumericV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedQM31SamplerDigits.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedQM31SamplerDigits"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedQM31SamplerCarrier.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedQM31SamplerCarrier"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SourceSamplerByteRank.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SourceSamplerByteRank"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/SemDecision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.SemDecision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/SemRounds.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.SemRounds"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/SemClosed.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.SemClosed"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/R599CanonicalFieldTuple.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.R599CanonicalFieldTuple"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WideTower.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WideTower"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisFormal/CircleGroupOrder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisFormal.CircleGroupOrder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/SlackStatement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.SlackStatement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/QuerySampler.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.QuerySampler"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port5Q1_GeometryTerminal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_GeometryTerminal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedCurrentCM31Mul.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedCurrentCM31Mul"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S7Kani3BasisTotal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S7Kani3BasisTotal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S7JoinBasisIdentity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S7JoinBasisIdentity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FoldGeometryBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FoldGeometryBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_InverseExplicitMul.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_InverseExplicitMul"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17FibrePointLineNodeActual.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17FibrePointLineNodeActual"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Decoded.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Decoded"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1SemanticCodeVerifyV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticCodeVerifyV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1SemanticCodeFinishExactV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticCodeFinishExactV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1SemanticCodeBeginExactV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticCodeBeginExactV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1SemanticCodePublicTranscriptExactV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1SemanticCodePublicTranscriptExactV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkC_FirstAuthentication.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkC_FirstAuthentication"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port4b-20261023/Port4B_CallerJoin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_CallerJoin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_SecondProvenance.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_SecondProvenance"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_Silent.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_Silent"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_Residual.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_Residual"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_RetainedReader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_RetainedReader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_SecondSkeleton.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_SecondSkeleton"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_SourceCurrentBatch.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_SourceCurrentBatch"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_BatchNative.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_BatchNative"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_BatchSyntax.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_BatchSyntax"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkC_Authentication.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkC_Authentication"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SdkD_ReaderQueries.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SdkD_ReaderQueries"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_PairCheckpointLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_PairCheckpointLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_FinishLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_FinishLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_PreparedCut.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_PreparedCut"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_ConsSource.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_ConsSource"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_Cuts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_Cuts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_EffectDictionary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_EffectDictionary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_ReaderSkeleton.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_ReaderSkeleton"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R9DeployedBinaryExperiment.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R9DeployedBinaryExperiment"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R16DecisionCheckpoint.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R16DecisionCheckpoint"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R20PoolStatementAgreement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R20PoolStatementAgreement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_RunPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_RunPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_OuterLower.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_OuterLower"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawK_SemanticHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawK_SemanticHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S1CurrentPrepareCodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1CurrentPrepareCodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3U_VerifyHead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3U_VerifyHead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_PreparePure.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_PreparePure"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_AcceptedReplacement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_AcceptedReplacement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/LogA_Dependencies.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "LogA_Dependencies"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_ParsedRows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_ParsedRows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Decision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Decision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3S_RoundUnique.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3S_RoundUnique"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3T_Checked.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3T_Checked"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
