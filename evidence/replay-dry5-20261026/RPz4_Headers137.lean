import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkOwnedGuardAcquireV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkOwnedGuardAcquireV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkOwnedReachabilityV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkOwnedReachabilityV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S126SdkFixedInputCurrentV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S126SdkFixedInputCurrentV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkErrorBufferFrameV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkErrorBufferFrameV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkBorrowedEquivalenceV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkBorrowedEquivalenceV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkFixedInputCallerV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkFixedInputCallerV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkCheckpointSizeTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkCheckpointSizeTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
