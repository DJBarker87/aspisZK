import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkOwnedBorrowTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkOwnedBorrowTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2OwnedSourceInstallationV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2OwnedSourceInstallationV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkBorrowedReferenceV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkBorrowedReferenceV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkSourceScanV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkSourceScanV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkAdmittedCallerV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkAdmittedCallerV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedTx1Reachability.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedTx1Reachability"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
