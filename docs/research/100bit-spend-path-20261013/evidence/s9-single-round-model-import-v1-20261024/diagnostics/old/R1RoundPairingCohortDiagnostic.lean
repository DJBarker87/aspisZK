import R1RoundPairing
import Lean
open Lean Elab Command
/- Read-only environment diagnostic, not a mathematical/security proof. -/
run_elab do
  let env ← getEnv
  let wanted : Array Name := #[`R1RoundPairing]
  let rows := env.constants.toList.filterMap (fun entry => do
    let idx ← env.getModuleIdxFor? entry.1
    let owner := env.header.moduleNames[idx.toNat]!
    if wanted.contains owner then
      some (entry.1.toString,
        s!"DECL|{owner}|{entry.1}|{entry.2.isTheorem}|{hash entry.2.type}|{hash (entry.2.value? true)}")
    else none)
  (rows.toArray.qsort (fun a b => a.1 < b.1)).forM (fun row => logInfo row.2)
