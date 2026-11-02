import Lean
import JGx_SdkAfterValidationEq
import NEP_WALKER
open Lean Elab Command
run_cmd do
 let env := (← getEnv).setExporting false
 for n in #[`AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3, `AspisR1.JGx_SdkAfterValidationEq.source] do
  logInfo m!"NEP_SDK {n}: checked={(env.checked.get.find? n).isSome} find={(env.find? n).isSome} module={env.getModuleIdxFor? n}"
 let n := `AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3
 for data in env.header.moduleData do
  for c in data.constants do
   if c.name == n then logInfo m!"NEP_SERIALIZED_FOUND {c.name}"
run_cmd NEP.audit `AspisR1.JGx_SdkAfterValidationEq.source "NEP_Sdk"
#print axioms AspisR1.JGx_SdkAfterValidationEq.source
