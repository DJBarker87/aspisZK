import Lean
open Lean
-- Inspect one serialized module at a time, freeing its region before the next.
unsafe def NEP_scan : IO Unit := do
 let dir : System.FilePath := "/home/dombarker/project-offloads/codex-cx-walker-cache-20261102/objects"
 for entry in ← dir.readDir do
  if entry.path.extension != some "olean" then continue
  let (data, region) ← readModuleData entry.path
  for c in data.constants do
   let refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
   if refs.contains `AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3 then
    IO.println s!"NEP_SERIALIZED_PARENT {entry.path.fileName}: {c.name}; isModule={data.isModule}"
   if c.name == `AdapterRw.r1_pool_adapter.owned.stage2_owned then
    IO.println s!"NEP_SERIALIZED_OWNER {entry.path.fileName}; isModule={data.isModule}"
  region.free
#eval NEP_scan
