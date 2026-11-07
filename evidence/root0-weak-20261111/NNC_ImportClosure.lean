import Lean
open Lean
/-- Read cached module headers without importing their declarations. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut seen : Std.HashSet Name := {}
  let mut todo : List (Name × Name) := [(`NNC_ImportClosure, `RPx_FJv_DRelease)]
  while !todo.isEmpty do
    let (parent, name) := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    try
      let file ← findOLean name
      let privateFile := System.FilePath.mk (file.toString ++ ".private")
      let serverFile := System.FilePath.mk (file.toString ++ ".server")
      let files := if ← privateFile.pathExists then #[file, serverFile, privateFile] else #[file]
      let parts ← readModuleDataParts files
      let irFile := file.withExtension "ir"
      let parts ← if ← irFile.pathExists then do
        let ir ← readModuleData irFile
        pure (parts.push ir)
      else pure parts
      for (data, _) in parts do
        for i in data.imports do
          todo := (name, i.module) :: todo
    catch e => IO.println s!"MISSING {parent} -> {name}: {e}"
  IO.println s!"modules {seen.size}"
  return 0
