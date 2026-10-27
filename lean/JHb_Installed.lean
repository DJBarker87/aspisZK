import IDa_Deployed
import JHb_Programs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_Installed
open Aeneas Aeneas.Std Result DrvC_Installation
/-- The deployed installation has no fixed Pool-ID field: the source slot is
preserved from missing.adapter. This equation records that boundary exactly. -/
theorem pool_slot {C : Type} (missing : IDa_Deployed.Uninstalled C)
    (err : C) (reservation : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (IDa_Deployed.deployedConfiguration missing err reservation)).op45 =
      missing.adapter.op45 := rfl
#print axioms pool_slot

def select {C : Type} (missing : IDa_Deployed.Uninstalled C) : IDa_Deployed.Uninstalled C :=
  {missing with adapter:={missing.adapter with
    op45:=ok JHb_Programs.pool,op46:=ok JHb_Programs.registry}}

theorem selected_pool {C : Type} (missing : IDa_Deployed.Uninstalled C)
    (err : C) (reservation : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (IDa_Deployed.deployedConfiguration (select missing) err reservation)).op45 =
      ok JHb_Programs.pool := rfl
#print axioms selected_pool

theorem selected_registry {C : Type} (missing : IDa_Deployed.Uninstalled C)
    (err : C) (reservation : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (IDa_Deployed.deployedConfiguration (select missing) err reservation)).op46 =
      ok JHb_Programs.registry := rfl
#print axioms selected_registry
end AspisR1.JHb_Installed
end
