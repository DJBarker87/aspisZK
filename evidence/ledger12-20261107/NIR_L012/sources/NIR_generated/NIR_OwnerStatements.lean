import NIR_COMBINED_IMPORT
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "NIR_AUDIT_ROOTS.json"))
  let roots ← IO.ofExcept (manifest.getObjValAs? (Array String) "roots")
  let env ← getEnv
  for root in roots do
    let name := root.toName
    let some c := env.find? name | throwError "missing required root {root}"
    let some idx := env.getModuleIdxFor? name | throwError "missing owner {root}"
    let statement ← PrettyPrinter.ppExpr c.type
    let row := Json.mkObj [("root",toJson root),
      ("owner_module",toJson env.header.moduleNames[idx]!.toString),
      ("obligation_statement",toJson statement.pretty)]
    logInfo m!"NIR_OWNER {row.compress}"
