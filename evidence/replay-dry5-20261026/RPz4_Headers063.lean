import Lean
open Lean Elab Command
run_cmd do
  do
    let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Rc7_Top.olean"
    logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Rc7_Top"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  logInfo "RPZ4_HEADERS_COMPLETE"
