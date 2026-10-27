import JHe_Configuration
import IDa_Deployed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_HeadlineConfiguration
open Aeneas Aeneas.Std Result

def missing {C : Type} (m : JHe_InstalledData.Uninstalled C) : IDa_Deployed.Uninstalled C where
  adapter:=m.adapter
  currentBase:=m.currentBase
  stageBase:=m.stageBase
  reserved:=m.reserved
  query:=m.query
  geometry:=m.geometry

theorem seed {C : Type} (m : JHe_InstalledData.Uninstalled C) (r : NP6_StdModel.Reservation) :
    JHe_InstalledData.seed m r=IDa_Deployed.seed (missing m) r := by
  rfl
#print axioms seed

theorem installed {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    JHe_InstalledData.deployedConfiguration m err r=
      IDa_Deployed.deployedConfiguration (missing m) err r := by
  unfold JHe_InstalledData.deployedConfiguration IDa_Deployed.deployedConfiguration
  rw [seed]
#print axioms installed

theorem source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHe_Configuration.value adapter stage=
      IDa_Deployed.deployedConfiguration (missing (JHe_Configuration.missing adapter stage)) () (.Ok ()) :=
  installed _ _ _
#print axioms source
end AspisR1.JHe_HeadlineConfiguration
end
