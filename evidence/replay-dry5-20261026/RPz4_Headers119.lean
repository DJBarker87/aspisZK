import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeLateWordConstantsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeLateWordConstantsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeSnapshotDecoderPart12FramesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeSnapshotDecoderPart12FramesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6SourcePaymentCommonDecodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6SourcePaymentCommonDecodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeAfterstateValidatorTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeAfterstateValidatorTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeDigestEncodeSourceEqV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeDigestEncodeSourceEqV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2K_AfterstatePrefix.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2K_AfterstatePrefix"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6AfterstateDecoderPart8FramesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6AfterstateDecoderPart8FramesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6SourcePaymentHeaderTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6SourcePaymentHeaderTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_SampleBlockAssociation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_SampleBlockAssociation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
