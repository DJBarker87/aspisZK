import Lean
open Lean
-- Direct object reader: never constructs a merged project environment.
-- Serialize before freeing each module's regions; no mapped object escapes.
unsafe def main (args : List String) : IO Unit := do
  let stdout ← IO.getStdout
  let input ← IO.FS.lines args[0]!
  for line in input do
    let fields := line.splitOn "\t"
    let mod := fields[0]!
    let path := fields[1]!
    let (base, region) ← readModuleData path
    let mut parts := #[(base, region)]
    if base.isModule then
      let more ← readModuleDataParts #[path, path ++ ".server", path ++ ".private"]
      CompactedRegion.free region
      parts := more
    let names := parts.foldl (fun acc p => acc ++ p.1.constNames.map Name.toString) #[]
    let extras := parts.foldl (fun acc p => acc ++ p.1.extraConstNames.map Name.toString) #[]
    let imports := parts.foldl (fun acc p => acc ++ p.1.imports.map (fun i => i.module.toString)) #[]
    let j := Json.mkObj [("module", toJson mod), ("path", toJson path),
      ("names", toJson names), ("extras", toJson extras), ("imports", toJson imports)]
    stdout.putStrLn j.compress
    stdout.flush
    for p in parts.reverse do
      CompactedRegion.free p.2
