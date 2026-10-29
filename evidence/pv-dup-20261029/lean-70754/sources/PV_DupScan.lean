import Lean
open Lean
-- Direct object reader: never constructs a merged project environment.
-- Serialize before freeing each module's regions; no mapped object escapes.
@[noinline] unsafe def inspect (line : String) : IO (Array CompactedRegion) := do
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
    let names := parts.foldl (fun acc p => acc ++ p.1.constNames.map Name.toString) #[]
    let extras := parts.foldl (fun acc p => acc ++ p.1.extraConstNames.map Name.toString) #[]
    let imports := parts.foldl (fun acc p => acc ++ p.1.imports.map (fun i => i.module.toString)) #[]
    let j := Json.mkObj [("module", toJson mod), ("path", toJson path),
      ("names", toJson names), ("extras", toJson extras), ("imports", toJson imports)]
    stdout.putStrLn j.compress
    stdout.flush
    return parts.map (·.2)

unsafe def main (args : List String) : IO Unit := do
  let input ← IO.FS.lines args[0]!
  for line in input do
    let regions ← inspect line
    for region in regions.reverse do
      CompactedRegion.free region
