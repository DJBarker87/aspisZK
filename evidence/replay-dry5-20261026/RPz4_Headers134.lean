import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkReadyAcquireV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkReadyAcquireV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S126SdkSizedAccountExportV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S126SdkSizedAccountExportV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkFixedImageFirstV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkFixedImageFirstV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
