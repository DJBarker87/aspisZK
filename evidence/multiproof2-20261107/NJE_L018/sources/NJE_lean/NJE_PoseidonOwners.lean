import NJA_COMBINED_IMPORT
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s := n.toString
  if (s.endsWith ".pow5" || s.endsWith ".apply_mat4_lazy" || s.endsWith ".external_linear_lazy" || s.endsWith ".internal_linear_lazy" || s.contains "Iterator.all") then
   if let some idx := env.getModuleIdxFor? n then
    logInfo m!"NJE_BODY {n} owner={env.header.moduleNames[idx]!} type={c.type} value={c.value? true}"
