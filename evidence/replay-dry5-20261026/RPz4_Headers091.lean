import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideMulSourceGraph.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideMulSourceGraph"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAQ_RawCM.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAQ_RawCM"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideField.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideField"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentWideQMMulM31V5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentWideQMMulM31V5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_PartialOracle.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_PartialOracle"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_NativeClassify.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_NativeClassify"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_AccountBinding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_AccountBinding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_Zero.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_Zero"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_Choice.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_Choice"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_RowsBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_RowsBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_OuterGoodLaws.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_OuterGoodLaws"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_BudgetTactic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_BudgetTactic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/DrvC_FirstPrograms.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DrvC_FirstPrograms"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_ObservedOpening.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_ObservedOpening"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_ObservedGeometry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_ObservedGeometry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_LineInputs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_LineInputs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-port5q1-20261024/Port5Q1_InstallPorts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port5Q1_InstallPorts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/SamplerWrapperPolicies.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.SamplerWrapperPolicies"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R15/ExactTowerChord.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R15.ExactTowerChord"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SecondFoldMatched.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SecondFoldMatched"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SecondFoldRestoration.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SecondFoldRestoration"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FirstFoldRestoration.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FirstFoldRestoration"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1InitialResponses.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1InitialResponses"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1RoundPairing.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RoundPairing"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/V3/DQDecodes.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.V3.DQDecodes"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/V3/BSOk.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.V3.BSOk"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ReseedBoundary.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ReseedBoundary"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PublicInitParse.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PublicInitParse"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/UniformStateFirstHit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.UniformStateFirstHit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1RawRoundCompletion.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RawRoundCompletion"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1QueryDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1QueryDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ActualRawLongDivisionCost.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ActualRawLongDivisionCost"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Basic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.Basic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/ToMathlib/Order/WithBot.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.ToMathlib.Order.WithBot"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/ToPoly/Degree.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.ToPoly.Degree"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/ToMathlib/Polynomial/Div.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.ToMathlib.Polynomial.Div"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Raw/Division.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.Raw.Division"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/ToPoly/Core.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.ToPoly.Core"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTT/FastMul.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTT.FastMul"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTT/FastMulLow.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTT.FastMulLow"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTTFast/Correctness/Pipeline.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTTFast.Correctness.Pipeline"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTTFast/FastMulLow.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTTFast.FastMulLow"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/SequentialFreshProgram.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SequentialFreshProgram"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRProgramTraversal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRProgramTraversal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawCutRecordedWordsExecutable.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawCutRecordedWordsExecutable"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralStageFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralStageFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralReadAtFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralReadAtFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawFullPublicRun.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawFullPublicRun"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawCompiledTranscript.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawCompiledTranscript"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawCompiledDecoderCompletion.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawCompiledDecoderCompletion"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawRecordedPublicSpendExtractorReturnedRelation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawRecordedPublicSpendExtractorReturnedRelation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawRecordedChecksSpendExtractor.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawRecordedChecksSpendExtractor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/LiteralFreshAbortComposition.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "LiteralFreshAbortComposition"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSConcreteByteDecoderBank.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSConcreteByteDecoderBank"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/DecodedFirstReadUnionBound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DecodedFirstReadUnionBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SubfieldBatchStage2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SubfieldBatchStage2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ConcreteProjection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ConcreteProjection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralSemanticExcludedLift.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralSemanticExcludedLift"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1GenericNoHitIndex.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1GenericNoHitIndex"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralMatchingSemanticData.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralMatchingSemanticData"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralSpendExtraction.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralSpendExtraction"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SemanticPrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SemanticPrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralSemanticTerminalBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralSemanticTerminalBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SpendDataMap.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SpendDataMap"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralOpeningGood.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralOpeningGood"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralGammaSample.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralGammaSample"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralQueryRhoSupport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralQueryRhoSupport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LiteralReadStability.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LiteralReadStability"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SelectedOpeningFunctionals.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SelectedOpeningFunctionals"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/MaskView.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.MaskView"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1AdapterReconstruct/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1AdapterReconstruct.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PublicExtractedRawBridge431.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PublicExtractedRawBridge431"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WithdrawalValidationAmount431.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WithdrawalValidationAmount431"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PublicRawAmountGuard.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PublicRawAmountGuard"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PublicRawCoreAgreement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PublicRawCoreAgreement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PublicSourceRawSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PublicSourceRawSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PublicByteCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PublicByteCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalCutWordProjection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalCutWordProjection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalCutTypedProjection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalCutTypedProjection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FoldedRecoveredWord.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FoldedRecoveredWord"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleIndexGeometry.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleIndexGeometry"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawByteCutStability.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawByteCutStability"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CommitmentRootFrames.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CommitmentRootFrames"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS2/DuplexInj.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS2.DuplexInj"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleNodeCodec.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleNodeCodec"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1FixedOffsetTarget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1FixedOffsetTarget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ParsedStateCollision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ParsedStateCollision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedInitialLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedInitialLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedSemanticLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedSemanticLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedReseedLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedReseedLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedOpeningLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedOpeningLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedQueryLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedQueryLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1JointUnifiedBound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1JointUnifiedBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1DecoderStateList.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1DecoderStateList"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/OpeningSamplerBounds.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.OpeningSamplerBounds"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/SlackDensity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.SlackDensity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS2/DuplexDecodes.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS2.DuplexDecodes"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0C/QueryCounting.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0C.QueryCounting"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/R417Q22SuccessLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.R417Q22SuccessLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
