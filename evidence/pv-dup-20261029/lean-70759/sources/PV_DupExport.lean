import Lean
open Lean
-- Direct object reader: never constructs a merged project environment.
-- Serialize before freeing each module's regions; no mapped object escapes.
@[noinline] unsafe def inspect (wanted : Std.HashSet String) (line : String) : IO (Array CompactedRegion) := do
    let stdout ← IO.getStdout
    let fields := line.splitOn "\t"
    let mod := fields[0]!
    let path := fields[1]!
    let (base, region) ← readModuleData path
    let mut parts := #[(base, region)]
    if base.isModule then
      let server ← CompactedRegion.read (α := ModuleData) (path ++ ".server") #[region]
      let priv ← CompactedRegion.read (α := ModuleData) (path ++ ".private") #[region, server.2]
      parts := parts.push server |>.push priv
    for p in parts do
      for c in p.1.constants do
        if wanted.contains c.name.toString then
          let j := Json.mkObj [("module",toJson mod), ("name",toJson c.name.toString),
            ("type",toJson (reprStr c.type)), ("value",toJson ((c.value? true).map reprStr)),
            ("level_params",toJson (c.levelParams.map Name.toString))]
          stdout.putStrLn j.compress
          stdout.flush
    return parts.map (·.2)

unsafe def main (args : List String) : IO Unit := do
  let wanted := (← IO.FS.lines args[1]!).foldl (fun s n => s.insert n) ({} : Std.HashSet String)
  let input ← IO.FS.lines args[0]!
  for line in input do
    let regions ← inspect wanted line
    for region in regions.reverse do
      CompactedRegion.free region
