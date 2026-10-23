import Lean
open Lean
#eval show IO Unit from do
  let input ← IO.getEnv "IMPORT_UNION_SCAN_INPUT"
  let some input := input | throw (IO.userError "IMPORT_UNION_SCAN_INPUT is required")
  for line in (← IO.FS.readFile input).splitOn "\n" do
    if line.isEmpty then continue
    let fields := line.splitOn "\t"
    let owner := fields[0]!
    let path : System.FilePath := fields[1]!
    let (data, _region) ← readModuleData path
    IO.println ("MODULE " ++ (Json.arr #[toJson owner, toJson path.toString,
      toJson (data.imports.map (fun i => i.module.toString))]).compress)
