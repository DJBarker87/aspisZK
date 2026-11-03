import Lean
open Lean
unsafe def main (_ : List String) : IO UInt32 := do
 for path in ["/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AdapterRwModel.olean", "/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects/AdapterRwModel.olean"] do
  let (data, region) ← readModuleData path
  for c in data.constants do
   if c.name.toString.startsWith "AdapterRw.r1_pool_adapter.owned.stage2_owned.match_" then
    IO.println s!"NER_MATCHER {path} {c.name}"
   if c.name == `AdapterRw.r1_pool_adapter.owned.stage2_owned then
    IO.println s!"NER_STAGE2 {path} {(c.value? true).map (fun e => e.getUsedConstants.map Name.toString)}"
  region.free
 return 0
