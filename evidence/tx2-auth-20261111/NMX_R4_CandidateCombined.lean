import NMX_R3_InstantiatedCombined
import NMX_R4_Authentication
import NMX_R4_BoxCoverage
open Lean Elab Command
#check RSL.Env.reservation
#check LIBB_V2Star.gate
#check LIBB_Tx2AuthGate.returnFunctional
#print axioms NMX_R4_Authentication.observed
#print axioms NMX_R4_Authentication.root
run_cmd do
 let env ← getEnv
 logInfo ("NMX_R4_MODULES " ++ (toJson (env.header.moduleNames.map Name.toString)).compress)
