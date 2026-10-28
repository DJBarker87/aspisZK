import NDO_JHe_InstalledData
import NDO_JHe_FinalInstallation
import RPv_IDa_Deployed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDO_InstalledIdentity
open Aeneas Aeneas.Std Result

/-- The same data-only uninstalled fields, interpreted by the headline owner. -/
def missing {C : Type} (m : JHe_InstalledData.Uninstalled C) : IDa_Deployed.Uninstalled C where
  adapter := m.adapter
  currentBase := m.currentBase
  stageBase := m.stageBase
  reserved := m.reserved
  query := m.query
  geometry := m.geometry

/-- Re-elaboration of JHe_HeadlineConfiguration.seed against RPx's owners. -/
theorem seed {C : Type} (m : JHe_InstalledData.Uninstalled C) (r : NP6_StdModel.Reservation) :
    JHe_InstalledData.seed m r = IDa_Deployed.seed (missing m) r := by
  rfl
#print axioms seed

/-- Re-elaboration of the existing installation identity, without a fixture import. -/
theorem installed {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    JHe_InstalledData.deployedConfiguration m err r =
      IDa_Deployed.deployedConfiguration (missing m) err r := by
  unfold JHe_InstalledData.deployedConfiguration IDa_Deployed.deployedConfiguration
  rw [seed]
#print axioms installed

/-- This is the exact FIp/IDa expression in RPx_Deployed.deployed.
It identifies the data configuration only; it does not construct a joint run. -/
theorem finalInstalled {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    FIp_Install.configuration err (IDa_Deployed.deployedConfiguration (missing m) err r) r =
      JHe_InstalledData.deployedConfiguration m err r := by
  rw [← installed]
  exact JHe_FinalInstallation.source m err r
#print axioms finalInstalled
end AspisR1.NDO_InstalledIdentity
end
