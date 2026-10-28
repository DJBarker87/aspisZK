import Lean
import RPx_Deployed
import NDO_Joint
import NDO_InstalledIdentity
set_option autoImplicit false
open Lean Elab Command

namespace AspisR1.NDR_CombinedAudit
open Aeneas Aeneas.Std Result
/-- The exact installed configuration underlying the witness's first and second
native functions is the headline's final FIp/IDa configuration at these data. -/
theorem fixtureInstalled (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHe_Natives.configuration base stage =
      FIp_Install.configuration ()
        (IDa_Deployed.deployedConfiguration
          (NDO_InstalledIdentity.missing
            (JHe_Configuration.missing (JHe_SdkLeaves.install base) stage))
          () (.Ok ())) (.Ok ()) := by
  exact (NDO_InstalledIdentity.finalInstalled
    (JHe_Configuration.missing (JHe_SdkLeaves.install base) stage) () (.Ok ())).symm
#print axioms fixtureInstalled
end AspisR1.NDR_CombinedAudit

-- Submit only after every NDO witness dependency passes.
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
    logInfo m!"NDR_SAME_WRAPPER_CONSTANTS {root}"
  logInfo m!"NDR_CLOSURE_MODULE_COUNT {env.header.modules.size}"
  logInfo "NDR_COMBINED_COMPLETE"
