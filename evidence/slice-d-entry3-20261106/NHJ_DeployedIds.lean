import NHJ_IdPacket
import NGK_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace NHJ_DeployedIds
open Aeneas Aeneas.Std Result
/-- Bind the actual uninstalled adapter fields that the deployed headline takes.
Other uninstalled fields remain the caller's original values. -/
def bindNativeIds {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) : AspisR1.IDa_Deployed.Uninstalled E :=
  {missing with adapter := NHJ_IdPacket.install missing.adapter devnet}

def configuration {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :=
  AspisR1.FIp_Install.configuration indexError
    (AspisR1.IDa_Deployed.deployedConfiguration (bindNativeIds missing devnet) indexError reservation)
    reservation

theorem pool_actual {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    (configuration missing devnet indexError reservation).adapter.op45 =
      ok (NHJ_IdPacket.pool devnet) := by rfl

theorem registry_actual {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    (configuration missing devnet indexError reservation).adapter.op46 =
      ok (NHJ_IdPacket.registry devnet) := by rfl
#print axioms pool_actual
#print axioms registry_actual
end NHJ_DeployedIds
