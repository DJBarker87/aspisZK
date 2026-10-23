import SelectorArrayMapRuntimeSlice
import ExtractedCurrentQM31Exact
import ExtractedCurrentQM31Tower
import AspisV8R17.QuadraticTowerOperations
import AspisV8R17.QM31WordResidues
import CurrentWideMulExactProduct
import CurrentWideMulM31V13
import Lean
open Lean Elab Command
/-- Read-only environment diagnostic, not a mathematical/security proof. -/
run_elab do
  let env ← getEnv
  let wanted : Array Name := #[`SelectorArrayMapRuntimeSlice,`ExtractedCurrentQM31Exact,
    `ExtractedCurrentQM31Tower,`AspisV8R17.QuadraticTowerOperations,
    `AspisV8R17.QM31WordResidues,`CurrentWideMulExactProduct,`CurrentWideMulM31V13]
  let mut rows : Array (String × String) := #[]
  for (name,ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!
      if wanted.contains owner then
        rows := rows.push (name.toString,
          s!"DECL|{owner}|{name}|{ci.isTheorem}|{hash ci.type}|{hash (ci.value? true)}")
  for row in rows.qsort (fun a b => a.1 < b.1) do
    logInfo row.2
