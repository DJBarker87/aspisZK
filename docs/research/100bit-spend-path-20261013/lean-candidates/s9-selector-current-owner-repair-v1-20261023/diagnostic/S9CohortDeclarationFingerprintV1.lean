import SelectorArrayMapRuntimeSlice
import ExtractedCurrentQM31Exact
import ExtractedCurrentQM31Tower
import AspisV8R17.QuadraticTowerOperations
import AspisV8R17.QM31WordResidues
import CurrentWideMulExactProduct
import CurrentWideMulM31V13
import Lean
open Lean Elab Command
/- Read-only environment diagnostic, not a mathematical/security proof. -/
run_elab do
  let env ← getEnv
  let wanted : Array Name := #[`SelectorArrayMapRuntimeSlice,`ExtractedCurrentQM31Exact,
    `ExtractedCurrentQM31Tower,`AspisV8R17.QuadraticTowerOperations,
    `AspisV8R17.QM31WordResidues,`CurrentWideMulExactProduct,`CurrentWideMulM31V13]
  let rows := env.constants.toList.filterMap (fun entry => do
    let idx ← env.getModuleIdxFor? entry.1
    let owner := env.header.moduleNames[idx.toNat]!
    if wanted.contains owner then
      some (entry.1.toString,
        s!"DECL|{owner}|{entry.1}|{entry.2.isTheorem}|{hash entry.2.type}|{hash (entry.2.value? true)}")
    else none)
  (rows.toArray.qsort (fun a b => a.1 < b.1)).forM (fun row => logInfo row.2)
