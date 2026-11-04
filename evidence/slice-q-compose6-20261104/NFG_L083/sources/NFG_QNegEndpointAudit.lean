import RPx_Deployed
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let found := env.constants.toList.filter (fun entry => entry.1.toString.endsWith ".QM31.neg")
 for (name, _) in found do
  logInfo m!"selected-closure-QM31-neg: {name}"
 logInfo m!"selected-closure-QM31-neg-count: {found.length}"
#print axioms AspisR1.RPx_Deployed.deployed
