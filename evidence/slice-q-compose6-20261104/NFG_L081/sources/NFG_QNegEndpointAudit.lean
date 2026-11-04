import RPx_Deployed
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (name, _) in env.constants.toList do
  let s := name.toString
  if s.endsWith ".QM31.neg" then
   logInfo m!"selected-closure-QM31-neg: {name}"
   count := count + 1
 logInfo m!"selected-closure-QM31-neg-count: {count}"
#print axioms AspisR1.RPx_Deployed.deployed
