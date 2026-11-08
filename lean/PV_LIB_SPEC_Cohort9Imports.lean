import Lean
open Lean
/-- Metadata inspection only. No declaration here is a privacy proof root. -/
@[noinline] unsafe def spec9ReadImports (path : System.FilePath) : IO (Array String × CompactedRegion) := do
  let (data,region) ← readModuleData path
  let imports := data.imports.map fun i => String.ofList i.module.toString.toList
  pure (imports,region)
unsafe def spec9CohortImports : IO Unit := do
  let dir := "/home/dombarker/project-offloads/codex-pv-lib-spec-20261107/"
  let paths ← match Json.parse (← IO.FS.readFile (dir ++ "session9-lanea-paths.json")) with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let mut todo := ["PV_LIB_A_StoreActionMachine"]
  let mut seen : Std.HashSet String := {}
  let mut rows : Array Json := #[]
  let mut regions : Array CompactedRegion := #[]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    unless seen.contains name do
      seen := seen.insert name
      let path ← match (paths.getObjValAs? String name) with
        | .ok p => pure p
        | .error e => throw (IO.userError (name ++ ": " ++ e))
      let (imports,region) ← spec9ReadImports path
      rows := rows.push (Json.mkObj [("module",toJson name),("imports",toJson imports)])
      todo := imports.toList ++ todo
      regions := regions.push region
  IO.FS.writeFile (dir ++ "evidence/session9-lanea-import-graph.json") (Json.arr rows).compress
  IO.println s!"Inspected {rows.size} module import headers; retained {regions.size} regions"
#eval spec9CohortImports
