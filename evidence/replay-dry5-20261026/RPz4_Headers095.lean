import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1TypedRecoveryStability.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1TypedRecoveryStability"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalTypedOpening.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalTypedOpening"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1LaterTableStability.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1LaterTableStability"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1Merkle32Path.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1Merkle32Path"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1RecordedRecoveryWitness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RecordedRecoveryWitness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleLogExtension.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleLogExtension"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS2/DuplexDensity.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS2.DuplexDensity"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedInitialDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedInitialDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedSemanticDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedSemanticDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedReseedDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedReseedDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedOpeningDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedOpeningDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedQueryDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedQueryDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1JointUnifiedDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1JointUnifiedDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedLabels.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedLabels"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PublicInitAbsorbSeparation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PublicInitAbsorbSeparation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1JointUnifiedLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1JointUnifiedLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1BackgroundOwnMap.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1BackgroundOwnMap"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FS2/DuplexWalk.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FS2.DuplexWalk"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/R411EqualLegalQueryMass.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.R411EqualLegalQueryMass"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/GuardedFirstRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.GuardedFirstRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/SemD2Glue.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.SemD2Glue"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SelectedPrefixRead.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SelectedPrefixRead"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisFormal/CircleFibreRoots.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisFormal.CircleFibreRoots"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1BatchedActualReducerFinish.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1BatchedActualReducerFinish"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S8OwnedP6QMParserTransport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S8OwnedP6QMParserTransport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1Qm31ArithmeticProbe/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1Qm31ArithmeticProbe.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/T2Nat_WeightsCongr.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "T2Nat_WeightsCongr"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S7JoinProductionBasis.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S7JoinProductionBasis"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S7Kani3CanonicalBackend.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S7Kani3CanonicalBackend"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S7Kani2OwnedRowRefinement.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S7Kani2OwnedRowRefinement"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S7Kani3CallerStep.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S7Kani3CallerStep"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port3_NativePendingBody.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port3_NativePendingBody"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbi2Extracted/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbi2Extracted.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/LoopPowersCandidateSteps.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "LoopPowersCandidateSteps"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytesETotal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytesETotal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytes3Reader.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytes3Reader"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbi5Weights.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbi5Weights"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbiSourceFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbiSourceFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortJoinSplitStd.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortJoinSplitStd"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbi3OwnedIter.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbi3OwnedIter"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/DecoderFiniteStartSupport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DecoderFiniteStartSupport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_Fissioned/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_Fissioned.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/WAdm_Fissioned/FunsExternal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "WAdm_Fissioned.FunsExternal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_GeometryGather.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_GeometryGather"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_GeometryStd.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_GeometryStd"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_BasisMeaning.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_BasisMeaning"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_ActualPair.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_ActualPair"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_ClosedResult.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_ClosedResult"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeParserTotal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeParserTotal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeVerifyState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeVerifyState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeLeafFrozen.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeLeafFrozen"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_ClaimsRows.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_ClaimsRows"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_DecodeCellTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_DecodeCellTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_TracePayload.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_TracePayload"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_LowDecodeInjective.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_LowDecodeInjective"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_CircleCell.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_CircleCell"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_RecordPacked.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_RecordPacked"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AspisR1DecodeKFullSuccessIndexedParser.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1DecodeKFullSuccessIndexedParser"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3N_ClaimPolynomial.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3N_ClaimPolynomial"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_CircleMeaning.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_CircleMeaning"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-parse-sem-20261025/ExtractedPrefixTypedFullCurrent.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPrefixTypedFullCurrent"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/EncoderConjugation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.EncoderConjugation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MixedLeafEncoding.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MixedLeafEncoding"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/IndexedCandidateOrdinaryRetainedBridgeV5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "IndexedCandidateOrdinaryRetainedBridgeV5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1NativeCompactBodyFrameV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1NativeCompactBodyFrameV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1SelectedMaskProbe/Funs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1SelectedMaskProbe.Funs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/D18Transport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "D18Transport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/MaskDuplexDecoder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.MaskDuplexDecoder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/R421UniformMasked31Block.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.R421UniformMasked31Block"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1InputPairSelection.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1InputPairSelection"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1AppendPath.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1AppendPath"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1M31EmbeddingTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1M31EmbeddingTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentOriginalPreparedInstallationV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentOriginalPreparedInstallationV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ToBytesP6StateInvariantV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ToBytesP6StateInvariantV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PaintSourceLimbsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PaintSourceLimbsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1WideToBytesIndexedCandidate/FunsNoResourceOptions.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ClaimBorrowedAbiTransportV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ClaimBorrowedAbiTransportV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6CurrentStage1CodecJoinV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6CurrentStage1CodecJoinV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6CurrentVerifierCarrierV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6CurrentVerifierCarrierV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ValuesOwnedChunkFormulaV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ValuesOwnedChunkFormulaV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1FrameArithmeticV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1FrameArithmeticV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port6CK_Suffix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port6CK_Suffix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port6CK_Factor.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port6CK_Factor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port6CK_QueryFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port6CK_QueryFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port6CK_Roots.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port6CK_Roots"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port6CK_Semantic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port6CK_Semantic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port6CK_Weights.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port6CK_Weights"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortRefineJoinCore.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortRefineJoinCore"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozen2Consumer.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozen2Consumer"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_LeafLoop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_LeafLoop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_AcceptedTail.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_AcceptedTail"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_AnyFalse.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_AnyFalse"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeP6Verify.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeP6Verify"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeKeyAdapters.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeKeyAdapters"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CandidateFieldParsers.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CandidateFieldParsers"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CandidateParserByteOrder.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CandidateParserByteOrder"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ParserArraySlice.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ParserArraySlice"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CandidateCM31Parser.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CandidateCM31Parser"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CandidateParserSupport.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CandidateParserSupport"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PowersP6GeneratedErasureV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PowersP6GeneratedErasureV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
