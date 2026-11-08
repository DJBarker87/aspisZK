import NNH_Tx2SlotTransport
open Lean in
run_cmd do
 let env ← getEnv
 for (n,info) in env.constants.toList do
  let s := n.toString
  if ((s.startsWith "NLP_NativeMerkle." || s.startsWith "NHT_FinishRelationModel." || s.startsWith "NHT_ResultPort.") && !s.contains "._" && !s.contains ".eq_") then
   match info with
   | .thmInfo _ => logInfo m!"{n}: {info.type}"
   | _ => pure ()
#print NLP_NativeMerkle.action
#print NIG_Slots.installed
