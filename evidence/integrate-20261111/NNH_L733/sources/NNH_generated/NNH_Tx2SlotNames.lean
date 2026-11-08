import NNH_CommonSlots
open Lean in
run_cmd do
 let env ← getEnv
 for (n,info) in env.constants.toList do
  let s := n.toString
  if ((s.startsWith "NFN_NEW_Geometry" || s.contains "NLB_Common" || s.contains "Port5Q1_Geometry" || s.startsWith "NIG_") && !s.contains "._") then
   match info with
   | .thmInfo _ => logInfo m!"{n}: {info.type}"
   | _ => pure ()
#print AspisR1.DrvC_Installation.stage
#print NFN_NEW_GeometryDictionary.adopted
#print AspisR1.IDa_Deployed.finish
#print AspisR1.Port4D_FinishInstall.finish
