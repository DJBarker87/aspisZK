import NNH_ValidateScanCongr
import NNH_Tx2Configuration
set_option autoImplicit false
noncomputable section
namespace NNH_ValidateSdkTail
open Aeneas Aeneas.Std AspisR1 AdapterRw

theorem source {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (reserve : NP6_StdModel.Reservation) :
 NNH_ValidateFission.scan (NNH_Tx2Configuration.sdk missing env err reserve)=
 NNH_ValidateFission.scan (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err reserve) env) := by
 apply NNH_ValidateScanCongr.same <;> rfl
#print axioms source
end NNH_ValidateSdkTail
