import NHG_COMBINED_IMPORT
#print AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary
#print AspisR1SemanticCallExtraction.r1_semantic.semantic_value
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s:=n.toString
  if (s.startsWith "AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary" ||
      s.startsWith "AspisR1SemanticCallExtraction.r1_semantic.semantic_value" ||
      (s.contains "RawExtractedSemanticCallOps" && s.endsWith "mul_eq_probe")) then
   logInfo m!"NHG_FINISH_OWNER {n}: {c.type}"
