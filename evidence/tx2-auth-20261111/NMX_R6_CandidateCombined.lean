import NMX_R4_CandidateCombined
import NMX_R6_SourceExact242
import NMX_R7_Fold241
open Lean Elab Command
#check RSL.Env.reservation
#check LIBB_V2Star.gate
#check LIBB_Tx2AuthGate.returnFunctional
#print axioms NMX_R6_Validation.root
#print axioms NMX_R6_SourceExact242.source
#print axioms NMX_R7_Fold241.fold
run_cmd do
 let env ← getEnv
 logInfo ("NMX_R6_MODULES " ++ (toJson (env.header.moduleNames.map Name.toString)).compress)
