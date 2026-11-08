import NMX_R6_CandidateCombined
import NMX_R9_StageTwo
import NMX_R8_Digest241
open Lean Elab Command
#check RSL.Env.reservation
#check LIBB_V2Star.gate
#check LIBB_Tx2AuthGate.returnFunctional
#print axioms NMX_R4_Authentication.root
#print axioms NMX_R6_Validation.root
#print axioms NMX_R9_Native241.full
#print axioms NMX_R9_StageTwo.root
#print axioms NMX_R9_StageTwo.source
run_cmd do
 let env ← getEnv
 logInfo ("NMX_R9_MODULES " ++ (toJson (env.header.moduleNames.map Name.toString)).compress)
