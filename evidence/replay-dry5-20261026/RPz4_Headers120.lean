import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeLateWordCastV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeLateWordCastV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeSnapshotFramePrependV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeSnapshotFramePrependV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6SourcePaymentDecodeHelpersV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6SourcePaymentDecodeHelpersV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2K_AfterstateLoop.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2K_AfterstateLoop"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6AfterstateDecoderPart12FramesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6AfterstateDecoderPart12FramesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_AssociationTactic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_AssociationTactic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
