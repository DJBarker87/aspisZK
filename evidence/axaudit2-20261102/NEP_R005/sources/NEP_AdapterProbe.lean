import Lean
import AdapterRwTypes
import AdapterRwModel
import AdapterRwCuts
open Lean Elab Command
run_cmd do
 let env := (← getEnv).setExporting false
 for n in #[`AdapterRw.r1_pool_adapter.owned.stage2_owned, `AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3] do
  logInfo m!"NEP_ADAPTER {n}: checked={(env.checked.get.find? n).isSome} find={(env.find? n).isSome} module={env.getModuleIdxFor? n}"
  if let some c := env.find? n then
   logInfo m!"NEP_KIND {n}: {c.ctorIdx} value={c.hasValue} refs={((c.value? true).map Expr.getUsedConstants).getD #[]}"
