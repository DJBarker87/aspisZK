import NBX_DeployedSelection
set_option autoImplicit false
noncomputable section
namespace NBX_InstalledOp23
open Aeneas Aeneas.Std Result AspisR1
/-- One retained field of the existing installed configuration; no native
body or extraction instance is inferred from this projection. -/
theorem retained {E : Type} (seed : DrvC_Installation.Configuration FIo_Install.W E)
    (err : E) (r : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (FIp_Install.configuration err
      (FIq_Install.configuration err (NBX_DeployedSelection.nativeSeed seed) r) r)).op23 =
      seed.adapter.op23 := rfl
#print axioms retained
end NBX_InstalledOp23
end
