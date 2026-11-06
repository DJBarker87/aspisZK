import NLM_DeployedOps
import NLM_SdkSlotProjection
set_option autoImplicit false
noncomputable section
namespace NLM_DeployedSlots
open Aeneas Aeneas.Std AspisR1 AspisR1.IDa_Deployed
/-- Audit only. The source slot is read from the headline's actual configuration;
no clone/encoder implementation law is invented by naming that configuration. -/
theorem clone_slot {C : Type} (missing : Uninstalled C) (indexError : C)
 (r : NP6_StdModel.Reservation) :
 (NLM_DeployedOps.ops missing indexError r).op35=
 (FIp_Install.configuration indexError (deployedConfiguration missing indexError r) r).adapter.op35 :=
 NLM_SdkSlotProjection.clone _
#print clone_slot
#print axioms clone_slot
end NLM_DeployedSlots
