import Lean
import RPx_Deployed
import NDO_Joint
import NDO_InstalledIdentity
set_option autoImplicit false
open Lean Elab Command

-- Prepared final target; submit only after every NDO witness dependency passes.
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NDO_Joint.source
#print axioms AspisR1.NDO_InstalledIdentity.finalInstalled
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`AspisR1.RPx_Deployed.deployed, `AspisR1.NDO_Joint.source] do
    let some info := env.checked.get.find? root | throwError "missing root {root}"
    let constants := info.type.getUsedConstants
    for required in #[`AspisR1.S2W_D189Wrappers.first, `AspisR1.S2W_D189Wrappers.second] do
      unless constants.contains required do
        throwError "root {root} does not directly mention {required}"
    logInfo m!"NDO_SAME_WRAPPER_CONSTANTS {root}"
  logInfo m!"NDO_CLOSURE_MODULE_COUNT {env.header.modules.size}"
  logInfo "NDO_COMBINED_COMPLETE"
