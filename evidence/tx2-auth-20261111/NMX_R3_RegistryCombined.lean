import NLX_COMBINED_IMPORT
import LIB_BUNDLE_IMPORT
import LIBB_V2Star
import NMX_R3_DecoderFold
import NMX_R3_RegistryRoot
import NMX_R3_RegistryIds
import NMX_R3_RegistryDataSource
import NMX_R3_RegistryPdaSource
open Lean Elab Command
#check RSL.Env.reservation
#check LIBB_V2Star.gate
#check LIBB_Tx2AuthGate.returnFunctional
#print axioms NMX_R3_RegistryRoot.root
#print axioms NMX_R3_RegistryNativeFold.native
#print axioms NMX_R3_DecoderFold.root
run_cmd do
 let env ← getEnv
 logInfo ("NMX_234_MODULES " ++ (toJson (env.header.moduleNames.map Name.toString)).compress)
