import NBX_HeadlineSelection
import NBX_InstalledOp23
set_option autoImplicit false
noncomputable section
namespace NBX_HeadlineOp23
open Aeneas Aeneas.Std Result AspisR1
/-- Actual headline missing/configuration field, composed from the checked
seed and installed projection. This is not a native extraction/frame law. -/
theorem field {E : Type} (m : IDa_Deployed.Uninstalled E) (err : E)
    (r : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (FIp_Install.configuration err
      (IDa_Deployed.deployedConfiguration (NBX_HeadlineSelection.nativeMissing m) err r) r)).op23 =
      m.adapter.op23 := by
  simpa only [IDa_Deployed.deployedConfiguration,NBX_HeadlineSelection.seed_instance] using
    NBX_InstalledOp23.retained (IDa_Deployed.seed m r) err r
#print axioms field
end NBX_HeadlineOp23
end
