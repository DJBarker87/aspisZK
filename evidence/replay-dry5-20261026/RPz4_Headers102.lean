import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17NarrowFunsB15ChunkPower.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17NarrowFunsB15ChunkPower"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17MinimalReverseBits.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17MinimalReverseBits"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17MinimalReverseBitsBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17MinimalReverseBitsBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableBasePowerProbe.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableBasePowerProbe"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17CircleCoordinateMulBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17CircleCoordinateMulBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_LeafActive.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_LeafActive"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_VerifyGuards.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_VerifyGuards"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3Q_VerifyLog.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3Q_VerifyLog"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port8EFF_Budget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port8EFF_Budget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawChecksAdaptiveCleanModelBin.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawChecksAdaptiveCleanModelBin"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawRecordedExtractorBranchTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawRecordedExtractorBranchTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawRecordedInitialCutObstruction.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawRecordedInitialCutObstruction"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortMapObservationsC6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortMapObservationsC6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortReachedRunC6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortReachedRunC6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortOpeningRewordC6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortOpeningRewordC6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortSemanticProjectionC6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortSemanticProjectionC6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/InitialPublicWalk.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "InitialPublicWalk"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1StrictReseedDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1StrictReseedDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1JointContextSound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1JointContextSound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EarlyPublicSelection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EarlyPublicSelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedSemanticCase.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedSemanticCase"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedReseedCase.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedReseedCase"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedPhases.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedPhases"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1RawRecordSplit.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RawRecordSplit"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawPublicOpeningWalkCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawPublicOpeningWalkCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedProtocol.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedProtocol"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedRecords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedRecords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedContinuation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedContinuation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CompletedView.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CompletedView"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1TableBeforeOrder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1TableBeforeOrder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedPhaseRecords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedPhaseRecords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1OpeningQueryTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1OpeningQueryTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedChainReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedChainReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedQueryReads.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedQueryReads"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalByteAddress.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalByteAddress"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/BackgroundAddressMap.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "BackgroundAddressMap"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ProgramLabelRestriction.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ProgramLabelRestriction"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedDispatchAddress.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedDispatchAddress"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedInitialCase.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedInitialCase"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedOpeningCase.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedOpeningCase"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedQueryCase.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedQueryCase"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedRhoCase.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedRhoCase"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleNodeLookupExt.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleNodeLookupExt"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleNodeRecordUnique.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleNodeRecordUnique"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleLeafLookupExt.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleLeafLookupExt"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleLeafRecordUnique.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleLeafRecordUnique"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSFinalMessageCandidateFilter.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSFinalMessageCandidateFilter"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSConcreteRootRecoveryDefinitions.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSConcreteRootRecoveryDefinitions"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRDenseCoeffVectorV6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRDenseCoeffVectorV6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSInterpolationRowBasis.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSInterpolationRowBasis"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSConstraintCount.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSConstraintCount"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSInterpolationBudget.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSInterpolationBudget"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/Interpolation/Dense/Correctness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GSRawStateCoefficientBridgeV6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GSRawStateCoefficientBridgeV6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/Filter.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Bivariate.GuruswamiSudan.Filter"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/PolynomialCorrectness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/Root/Common/Lemmas.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/InitialForwardEncoderBaseV9.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "InitialForwardEncoderBaseV9"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/InitialMessagePublicFilter.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "InitialMessagePublicFilter"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRConcreteRawRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRConcreteRawRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/WideExactNaturalBasisTriangularV14.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WideExactNaturalBasisTriangularV14"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisFormal/V5FriJohnsonListBound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisFormal.V5FriJohnsonListBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ListWitnessExtract.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ListWitnessExtract"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1IncrementalCandidateLoop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1IncrementalCandidateLoop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FiniteListCandidateMerge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FiniteListCandidateMerge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireRawBoundedCollision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireRawBoundedCollision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/LiteralDecoderPrefixRestore.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "LiteralDecoderPrefixRestore"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireRawCutLiteralAllFrames.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireRawCutLiteralAllFrames"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireConstructedWords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireConstructedWords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireRawByteLaterTableWords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireRawByteLaterTableWords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RWireRawByteCutTable.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RWireRawByteCutTable"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/RawJ_PublicRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawJ_PublicRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_Pure.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_Pure"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_FinishTail.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_FinishTail"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_Begin5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_Begin5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_RoundState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_RoundState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3R_SemanticChain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3R_SemanticChain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3J_SourceBlock.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3J_SourceBlock"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExq_FirstFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExq_FirstFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port9OR_P6Rows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port9OR_P6Rows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_Begin13.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_Begin13"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3V_SemanticValidated.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3V_SemanticValidated"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/DecodedFirstReadReplay.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DecodedFirstReadReplay"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/SAP_Op3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "SAP_Op3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hir_CallSuccess.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hir_CallSuccess"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1CurrentWide/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1CurrentWide.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Hiq_ReleaseRoute.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Hiq_ReleaseRoute"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/FinalCurveBranch.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.FinalCurveBranch"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/Cardinality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.Cardinality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/InitialSelection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.InitialSelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Data/Fin/BigOperators.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Data.Fin.BigOperators"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/NTTFast/Plan.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.NTTFast.Plan"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPolySplitFactorQuality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPolySplitFactorQuality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawCutLiteralAllFrames.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawCutLiteralAllFrames"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawCutConstructedWords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawCutConstructedWords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RawByteLaterTableWords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RawByteLaterTableWords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31ActualEightWideSampler.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31ActualEightWideSampler"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31EightLimbSuccessCount.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31EightLimbSuccessCount"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31RetryOutputMassNat.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31RetryOutputMassNat"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
