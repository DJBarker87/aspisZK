import Lake.Build.Trace
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let input ← IO.FS.readFile args[1]!
  let mut count := 0
  for line in input.splitOn "\n" do
    if line.isEmpty then continue
    if args[0]! == "hash" then
      let parts := line.splitOn "\t"
      let actual ← Lake.computeBinFileHash parts[0]!
      let expected := parts[1]!
      if toString actual != expected then
        throw <| IO.userError s!"Lake artifact hash mismatch: {parts[0]!}: {actual} != {expected}"
      count := count + 1
      if count % 1000 == 0 then IO.println s!"verified_progress={count}"
    else
      let (data, _region) ← readModuleData line
      IO.println (Json.mkObj [
        ("path", toJson line),
        ("isModule", toJson data.isModule),
        ("imports", toJson (data.imports.toList.map (fun i => i.module.toString)))
      ]).compress
      count := count + 1
  IO.println s!"verified_count={count}"
