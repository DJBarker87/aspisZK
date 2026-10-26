import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/BatchEval/Correctness.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPoly.Univariate.BatchEval.Correctness"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/RRActualTaylorSubstitutionV3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "RRActualTaylorSubstitutionV3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/Interpolation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.Interpolation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/AmbientCurve.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.AmbientCurve"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/RegularWeights.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.RegularWeights"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/Smooth.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.Smooth"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Wide/HenselCombinatorics.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Wide.HenselCombinatorics"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_Success.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_Success"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ClaimAllLoopsBoundedV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ClaimAllLoopsBoundedV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativePaymentHeaderTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativePaymentHeaderTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeForestCommonDecodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeForestCommonDecodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeForestPaymentBoxesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeForestPaymentBoxesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeLateHeaderLayoutV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeLateHeaderLayoutV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeSnapshotCodecV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeSnapshotCodecV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeLateChildDecodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeLateChildDecodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativePaymentFrameRecomposeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativePaymentFrameRecomposeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativePaymentCommonOutputV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativePaymentCommonOutputV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6PaymentTailChunkFrameV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6PaymentTailChunkFrameV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativePaymentCommonEncodeTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativePaymentCommonEncodeTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6FullForestEncoderNamedTypesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6FullForestEncoderNamedTypesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeForestHelpersV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeForestHelpersV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeSnapshotStoreV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeSnapshotStoreV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeAfterstateDecodedFramesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeAfterstateDecodedFramesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeAfterstateContentsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeAfterstateContentsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1CanonicalQRawUnified/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1CanonicalQRawUnified.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_RoundStepAssociation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_RoundStepAssociation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPolyFactorTwoChildBound.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPolyFactorTwoChildBound"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPolySplitStateClosure.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CompPolySplitStateClosure"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FiniteFieldNormalizedRootFactor.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FiniteFieldNormalizedRootFactor"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
