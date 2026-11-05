import NHG_COMBINED_IMPORT
set_option autoImplicit false
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s:=n.toString
  if ((s.contains "r1_semantic" && (s.endsWith "claims" || s.endsWith "semantic_round" || s.endsWith "semantic_rounds" || s.endsWith "verify_finish" || s.endsWith "verify_observed" || s.endsWith "mark")) || (s.contains "ValidatedRecord" && (s.endsWith "payload" || s.endsWith "decode_k")) ||
    s.contains "ClaimsUnrolledFinish" && s.endsWith "verify_finish") then
   logInfo m!"NHU_OWNER {n}: {c.type}"
