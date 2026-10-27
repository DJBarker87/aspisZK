import JHe_InstalledData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_FinalInstallation
open Aeneas Aeneas.Std Result

theorem source {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r=
      JHe_InstalledData.deployedConfiguration m err r := by
  cases m
  rfl
#print axioms source
end AspisR1.JHe_FinalInstallation
end
