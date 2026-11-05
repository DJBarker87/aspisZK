import NHG_COMBINED_IMPORT
set_option autoImplicit false
open Lean Elab Command in
run_cmd do
 let env←getEnv
 for (n,c) in env.constants.toList do
  let s:=n.toString
  if s.contains "UScalar" && (s.contains "shift" || s.contains "shr") && s.endsWith "spec" then
   logInfo m!"NHU_OWNER {n}: {c.type}"
#print FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
