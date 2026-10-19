import Lean

/- Read-only compiled-module provenance inspection, not a theorem or a replay. -/
open Lean

def main (args : List String) : IO Unit := do
  for path in args do
    let (data, _region) ← readModuleData path
    IO.println (Json.mkObj [
      ("path", toJson path),
      ("isModule", toJson data.isModule),
      ("imports", toJson (data.imports.toList.map (fun i => i.module.toString)))
    ]).compress
