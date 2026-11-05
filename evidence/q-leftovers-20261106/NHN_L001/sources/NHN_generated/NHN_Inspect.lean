import NHH_COMBINED_IMPORT
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let names := env.constants.toList.map Prod.fst
 for suffix in [".QM31.sub", ".QM31.neg", ".QM31.zero", ".CM31.neg", ".CodeField", ".QM31.asCodeField"] do
  let found := names.filter (fun n => n.toString.endsWith suffix)
  found.forM (fun n => logInfo m!"NHN_ENDPOINT {n}")
#print AspisR72Sampler.field.QM31
#print AspisR72Sampler.field.QM31.sub
#print AspisR72Sampler.field.QM31.try_inv
#print axioms AspisR1.RPx_Deployed.deployed
