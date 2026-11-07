import NMX_R3_RegistryCombined
import NMX_R3_Instantiated233
open Lean Elab Command
#check RSL.Env.reservation
#check LIBB_V2Star.gate
#check LIBB_Tx2AuthGate.returnFunctional
#print axioms NMX_R3_Instantiated233.library
#print axioms NMX_R3_Instantiated233.registry_packet
#print axioms NMX_R3_Instantiated233.native
#print axioms NMX_R3_Instantiated233.represented
run_cmd do
 let env ← getEnv
 logInfo ("NMX_233_MODULES " ++ (toJson (env.header.moduleNames.map Name.toString)).compress)
