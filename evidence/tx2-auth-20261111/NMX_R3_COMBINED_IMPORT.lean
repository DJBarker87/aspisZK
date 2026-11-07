import NLX_COMBINED_IMPORT
import NMX_R3_DecoderFold
import NMX_R3_NativeStep
open Lean Elab Command
#check RSL.Env.reservation
#print axioms NMX_R3_DecoderFold.root
#print axioms NMX_R3_DecoderFold.complete
#print axioms NMX_R3_NativeStep.accepted
run_cmd do
 let env ← getEnv
 logInfo ("NMX_R3_MODULES " ++ (toJson (env.header.moduleNames.map Name.toString)).compress)
