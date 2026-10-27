import JHe_InstalledData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_FinalInstallation
open Aeneas Aeneas.Std Result
theorem config_ext {F C : Type} (a b : DrvC_Installation.Configuration F C)
    (h0 : a.adapter=b.adapter)
    (h1 : a.currentBase=b.currentBase)
    (h2 : a.stageBase=b.stageBase)
    (h3 : a.finish=b.finish)
    (h4 : a.reserved=b.reserved)
    (h5 : a.query=b.query)
    (h6 : a.geometry=b.geometry)
    (h7 : a.boundaries=b.boundaries)
    (h8 : a.std=b.std)
    : a=b := by
  cases a
  cases b
  cases h0
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  rfl
#print axioms config_ext
theorem adapter {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).adapter=
      (JHe_InstalledData.deployedConfiguration m err r).adapter := by
  rfl
#print axioms adapter
theorem currentBase {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).currentBase=
      (JHe_InstalledData.deployedConfiguration m err r).currentBase := by
  rfl
#print axioms currentBase
theorem stageBase {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).stageBase=
      (JHe_InstalledData.deployedConfiguration m err r).stageBase := by
  rfl
#print axioms stageBase
theorem finish {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).finish=
      (JHe_InstalledData.deployedConfiguration m err r).finish := by
  rfl
#print axioms finish
theorem reserved {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).reserved=
      (JHe_InstalledData.deployedConfiguration m err r).reserved := by
  rfl
#print axioms reserved
theorem query {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query
theorem geometry {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).geometry=
      (JHe_InstalledData.deployedConfiguration m err r).geometry := by
  rfl
#print axioms geometry
theorem boundaries {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).boundaries=
      (JHe_InstalledData.deployedConfiguration m err r).boundaries := by
  rfl
#print axioms boundaries
theorem std {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).std=
      (JHe_InstalledData.deployedConfiguration m err r).std := by
  rfl
#print axioms std
theorem source {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r=
      JHe_InstalledData.deployedConfiguration m err r := by
  exact config_ext _ _ (adapter m err r) (currentBase m err r) (stageBase m err r) (finish m err r) (reserved m err r) (query m err r) (geometry m err r) (boundaries m err r) (std m err r)
#print axioms source
end AspisR1.JHe_FinalInstallation
end
