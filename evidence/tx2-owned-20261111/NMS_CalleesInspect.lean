import NFY_Part060
import NFY_Part057
import NFY_Part053
import NGE_NEQ_NullifierDomains
import NHJ_DeployedIds
import NMS_Interpreted
#check NFY_NFD_RequestOracle.array_result_state_effects
#check NFY_NFD_RequestOracle.result_state_effects
#check NFY_NEU_ReconstructAdopted.result_state_effects
#check NFY_NEQ_EncoderOracle.result_state_effects
#check NFY_NEY_EmitComposed.result_state_effects
#check NGE_NEQ_NullifierDomains.payment_result_frame
#check NFY_NEM_LaneReached.lane_instance
#print AspisR1.NFY_JHf_ReconstructionSlot.source
#check AspisR1.JHf_Carrier.toRequest
#check AspisR1.JHf_Carrier.toAuthenticatedAsq8Accounts
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  let s := n.toString
  if s.startsWith "AspisR1.JHf_Carrier" &&
     (s.endsWith "Request" || s.endsWith "AuthenticatedAsq8Accounts") then
   Lean.logInfo m!"{n}: {ci.type}"
