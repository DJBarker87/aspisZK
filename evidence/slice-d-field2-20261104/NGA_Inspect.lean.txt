import NFT_STAGE2_IMPORT
import RPx_Deployed
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  let s:=n.toString
  if s.endsWith ".WideExact.square" || s.endsWith ".QM31.square" || s.endsWith ".mul_u" || (s.contains 'Q' && s.endsWith "current_mul_exact") then logInfo m!"SELECTED {n}"
#print AspisR1SelectedMaskProbe.field.QM31.square
#print FIq_Native.field.WideExact.square
#print AspisR1Post25Sampler.field.WideExact.square
#print AspisR1.ExtractedMaskQM31Exact.current_mul_exact
#print AspisR1.FJm_QMSquare.value
#print axioms AspisR1.RPx_Deployed.deployed
