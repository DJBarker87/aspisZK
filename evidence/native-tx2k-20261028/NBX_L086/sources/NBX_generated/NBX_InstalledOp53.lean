import NBX_AdapterShape
import NBX_SdkRetention
set_option autoImplicit false
noncomputable section
namespace NBX_InstalledOp53
open Aeneas Aeneas.Std Result AspisR1
/-- One retained field of the existing installed configuration; no native
body or extraction instance is inferred from this projection. -/
theorem retained {E : Type} (seed : DrvC_Installation.Configuration FIo_Install.W E)
    (err : E) (r : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (FIp_Install.configuration err
      (FIq_Install.configuration err (NBX_DeployedSelection.nativeSeed seed) r) r)).op53 =
      seed.adapter.op53 := by
  rw [NBX_SdkRetention.emission,NBX_AdapterShape.adapter]
  rfl
#print axioms retained
end NBX_InstalledOp53
end
