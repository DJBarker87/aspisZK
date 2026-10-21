import Lean
import R22TotalRowPacketAudit
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let owner := env.header.moduleNames[idx.toNat]!
      if !(#["Init", "Lean", "Std", "Mathlib", "Batteries", "Aeneas", "Aesop", "Qq", "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient"]).contains (owner.toString.splitOn ".").head! then
        rows := rows.push (Json.arr #[toJson n.toString, toJson owner.toString])
  logInfo m!"INVENTORY {Json.compress (Json.arr rows)}"
