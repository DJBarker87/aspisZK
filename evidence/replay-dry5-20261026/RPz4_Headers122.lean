import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeLateDecoderFactoredV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeLateDecoderFactoredV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeLateWordReadV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeLateWordReadV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6NativeSnapshotDecodeHelpersV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6NativeSnapshotDecodeHelpersV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6SourceDigestRoundtripV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6SourceDigestRoundtripV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6FullSourceCodecV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6FullSourceCodecV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2K_Iterator.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2K_Iterator"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6AfterstateDecoderFramesV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6AfterstateDecoderFramesV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
