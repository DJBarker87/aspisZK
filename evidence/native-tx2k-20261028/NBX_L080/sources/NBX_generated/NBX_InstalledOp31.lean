import NBX_AdapterShape
import NBX_SdkRetention
set_option autoImplicit false
noncomputable section
namespace NBX_InstalledOp31
open Aeneas Aeneas.Std Result AspisR1
/-- One retained field of the existing installed configuration; no native
body or extraction instance is inferred from this projection. -/
theorem retained {E : Type} (seed : DrvC_Installation.Configuration FIo_Install.W E)
    (err : E) (r : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (FIp_Install.configuration err
      (FIq_Install.configuration err (NBX_DeployedSelection.nativeSeed seed) r) r)).op31 =
      seed.adapter.op31 := by
  have h := (NBK_DeployedCallbackSelection.registry (FIp_Install.configuration err (FIq_Install.configuration err (NBX_DeployedSelection.nativeSeed seed) r) r)).2.2.2.2.2.2.1
  rw [h,NBX_AdapterShape.adapter]
  rfl
#print axioms retained
end NBX_InstalledOp31
end
