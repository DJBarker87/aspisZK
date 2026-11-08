import Lean
open Lean
/-- Metadata inspection only. No declaration here is a privacy proof root. -/
@[noinline] unsafe def specReadImports (path : System.FilePath) : IO (Array String × CompactedRegion) := do
  let (data,region) ← readModuleData path
  let imports := data.imports.map fun i => String.ofList i.module.toString.toList
  pure (imports,region)
unsafe def specCohortImports : IO Unit := do
  let dir := "/home/dombarker/project-offloads/codex-pv-lib-spec-20261107/"
  let paths ← match Json.parse (← IO.FS.readFile (dir ++ "w4-module-paths.json")) with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let mut todo := ["PV_FN_THREAD_f170Statement","PV_FN_THREAD_f17OriginalStatement",
    "PV_FN_THREAD_f5OriginalStatement","PV_FN_THREAD_f2OriginalStatement"]
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
      let (imports,region) ← specReadImports path
      rows := rows.push (Json.mkObj [("module",toJson name),("imports",toJson imports)])
      todo := imports.toList ++ todo
      regions := regions.push region
  IO.FS.writeFile (dir ++ "evidence/session5-w4-import-graph.json") (Json.arr rows).compress
  IO.println s!"Inspected {rows.size} module import headers; retained {regions.size} regions"
#eval specCohortImports
