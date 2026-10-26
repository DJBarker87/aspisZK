import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkReadyCallerV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkReadyCallerV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
