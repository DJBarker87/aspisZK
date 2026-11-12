import AspisFailureBoundModel
/-! X5 check d (tool, nothing proved): the import closure of `AspisFailureBoundModel` as loaded from the objects,
one line per (module, direct import). Output file name is given by the option below via env var-free constant. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames
  let mut out : Array String := #[]
  for i in [0:names.size] do
    let m := names[i]!
    let md := env.header.moduleData[i]!
    if md.imports.isEmpty then out := out.push s!"{m}\t"
    for imp in md.imports do
      out := out.push s!"{m}\t{imp.module}"
  IO.FS.writeFile "import_graph.tsv" (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"modules {names.size} edges {out.size}"
