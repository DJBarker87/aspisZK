import CurrentWideQMSubV5
import Lean
open Lean Elab Command
/-- Read-only import/declaration diagnostic; not a mathematical theorem. -/
run_elab do
  let env ← getEnv
  let wanted : Name := `CurrentWideQMSubV5
  let mut rows : Array (String × String) := #[]
  for (name,ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!
      if owner==wanted then
        rows := rows.push (name.toString,
          s!"DECL|{owner}|{name}|{ci.isTheorem}|{hash ci.type}|{hash (ci.value? true)}")
  for row in rows.qsort (fun a b => a.1 < b.1) do
    logInfo row.2
