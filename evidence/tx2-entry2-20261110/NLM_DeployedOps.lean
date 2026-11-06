import RPx_Deployed
set_option autoImplicit false
noncomputable section
namespace NLM_DeployedOps
open Aeneas Aeneas.Std AspisR1 AspisR1.IDa_Deployed
/-- Exactly the sdk installation named by RPx_Deployed.deployed's extraction
hypothesis. This removes a free Ops dictionary from subsequent source folds;
it does not prove the retained extraction hypothesis for frozen Rust. -/
def ops {CoreError : Type} (missing : Uninstalled CoreError) (indexError : CoreError)
 (reservation : NP6_StdModel.Reservation) : AdapterRw.Ops :=
 DrvC_Installation.sdk (FIp_Install.configuration indexError
  (deployedConfiguration missing indexError reservation) reservation)
#print ops
end NLM_DeployedOps
