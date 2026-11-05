import RPx_Deployed
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let names := env.constants.toList.map Prod.fst
 for suffix in [".QM31.neg", ".CM31.inv", ".CM31.inv_with", ".QM31.inv", ".QM31.try_inv"] do
  let found := names.filter (fun n => n.toString.endsWith suffix)
  found.forM (fun n => logInfo m!"NHH_ADOPTED_ENDPOINT {suffix} {n}")
  logInfo m!"NHH_ADOPTED_ENDPOINT_COUNT {suffix} {found.length}"
#print axioms AspisR1.RPx_Deployed.deployed
