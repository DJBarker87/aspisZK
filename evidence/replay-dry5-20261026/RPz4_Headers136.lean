import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkOwnedGuardFrameV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkOwnedGuardFrameV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkOwnedDecodedReuseV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkOwnedDecodedReuseV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S126SdkFixedSavedCurrentV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S126SdkFixedSavedCurrentV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkMetadataFrameV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkMetadataFrameV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkCheckpointWriterV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkCheckpointWriterV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkCheckpointLengthV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkCheckpointLengthV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S2SdkSavedFirstV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S2SdkSavedFirstV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
