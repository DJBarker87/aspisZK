import Lean
import AdapterRwTypes
import AdapterRwModel
import AdapterRwCuts
import S2W_D189Wrappers
open Lean Elab Command
run_cmd do
 let env := (← getEnv).setExporting false
 for (n,c) in env.checked.get.constants.toList do
  let refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
  if refs.contains `AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3 then
   logInfo m!"NEP_DANGLING_PARENT {n} module={env.getModuleIdxFor? n}"
