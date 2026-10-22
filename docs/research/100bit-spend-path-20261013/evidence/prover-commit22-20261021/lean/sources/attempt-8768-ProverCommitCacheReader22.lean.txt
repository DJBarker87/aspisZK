import Lean
/-! Evidence utility: inspect retained compiled-module headers without
importing their declarations or claiming a source proof from cache presence. -/
set_option autoImplicit false
open Lean
#eval do
  let root := "/home/dombarker/project-offloads/codex-cx-prover-commit22-20261021/"
  let primary ← IO.FS.readFile (root ++ "r4-reader-input.txt")
  let input := primary ++ "/tmp/r1-circle-fallback-coalesced-native-closure-v8/objects/AspisV8R17/RawReducer.olean\n"
  let mut rows : Array Json := #[]
  for path in input.splitOn "\n" do
    if path.isEmpty then continue
    let (data, _) ← readModuleData path
    rows := rows.push (Json.mkObj [
      ("path",toJson path),
      ("imports",toJson (data.imports.map (fun (i : Lean.Import) => i.module.toString)))])
  IO.FS.writeFile (root ++ "r4-module-headers.json") (Json.pretty (toJson rows))
  IO.println s!"Inspected {rows.size} retained module headers; no imported theorems."
