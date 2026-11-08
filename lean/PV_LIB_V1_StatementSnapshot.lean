import Lean
open Lean
/-- Retain kernel expressions for exact root-type comparison across cohorts. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  if args.head? == some "imports" then
    let .ok j := Json.parse (← IO.FS.readFile (args[1]!)) | return 2
    let .ok paths := fromJson? (α := Array String) j | return 2
    for path in paths do
      let (data, _) ← readModuleData path
      IO.println ((Json.mkObj [("path", toJson path),
        ("imports", toJson (data.imports.map fun i => i.module.toString))]).compress)
    return 0
  let input ← IO.FS.readFile (args.headD "snapshot.json")
  let .ok j := Json.parse input | return 2
  let .ok modules := (j.getObjValAs? (Array String) "modules") | return 2
  let .ok roots := (j.getObjValAs? (Array String) "roots") | return 2
  let env ← importModules (modules.map fun n =>
    ({module := n.toName, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  let env := env.setExporting false
  let mut failed := false
  for root in roots do
    match env.find? root.toName with
    | none =>
      IO.println ((Json.mkObj [("root", toJson root), ("missing", toJson true)]).compress)
      failed := true
    | some info =>
      IO.println ((Json.mkObj [("root", toJson root),
        ("type", toJson (reprStr info.type)),
        ("level_params", toJson (info.levelParams.map Name.toString))]).compress)
  return if failed then 1 else 0
#print axioms main
