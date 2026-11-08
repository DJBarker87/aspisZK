import NNH_HostExec
import NNH_ExactRemainingTypes
import NLB_CommonTransport
set_option autoImplicit false
open AspisR1
#print NJC_ClosedCalls.geometry
run_cmd do
 let env ← Lean.getEnv
 for (n,info) in env.constants.toList do
  if n.toString.startsWith "NJC_ClosedCalls." || n.toString.startsWith "NLB_CommonTransport." then
   Lean.logInfo m!"{n}: {info.type}"
#print NJJ_Common.install
#print NJJ_Common.run
#print NLB_Parent.finish
#print NHT_PacketOps.query
#print Port3_QueryStage.query
#check Op5T_Concrete.stage_source
