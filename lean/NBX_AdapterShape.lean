import NBX_DeployedSelection
set_option autoImplicit false
noncomputable section
namespace NBX_AdapterShape
open Aeneas Aeneas.Std Result AspisR1
/-- Closed form of the adapter component. The installation changes only
clone/key fields of this component; unrelated configuration terms stay opaque. -/
theorem adapter {E : Type} (seed : DrvC_Installation.Configuration FIo_Install.W E)
    (err : E) (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err
      (FIq_Install.configuration err (NBX_DeployedSelection.nativeSeed seed) r) r).adapter =
      (CPP_Install.configuration (NBX_DeployedSelection.nativeSeed seed)).adapter := rfl
#print axioms adapter
end NBX_AdapterShape
end
