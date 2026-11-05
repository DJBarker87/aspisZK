import NHG_COMBINED_IMPORT
set_option autoImplicit false
#print AspisR1SemanticCallExtraction.r1_semantic.claims
#print AspisR1SemanticCallExtraction.r1_semantic.semantic_round
#print AspisR1SemanticCallExtraction.r1_semantic.semantic_rounds
#print AspisR1SemanticCallExtraction.r1_semantic.verify_finish
#print AspisR1SemanticCallExtraction.r1_semantic.verify_observed
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s:=n.toString
  if ((s.contains "ValidatedRecord" && (s.endsWith "payload" || s.endsWith "decode_k")) ||
    s.contains "ClaimsUnrolledFinish" && s.endsWith "verify_finish") then
   logInfo m!"NHU_OWNER {n}: {c.type}"
