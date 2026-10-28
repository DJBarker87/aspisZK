import NDO_JHe_InstalledData
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
theorem query_ext (a b : Port3_NativeQueryBody.Ops)
    (h0 : @Port3_NativeQueryBody.Ops.op0 a = @Port3_NativeQueryBody.Ops.op0 b)
    (h1 : @Port3_NativeQueryBody.Ops.op1 a = @Port3_NativeQueryBody.Ops.op1 b)
    (h2 : @Port3_NativeQueryBody.Ops.op2 a = @Port3_NativeQueryBody.Ops.op2 b)
    (h3 : @Port3_NativeQueryBody.Ops.op3 a = @Port3_NativeQueryBody.Ops.op3 b)
    (h4 : @Port3_NativeQueryBody.Ops.op4 a = @Port3_NativeQueryBody.Ops.op4 b)
    (h5 : @Port3_NativeQueryBody.Ops.op5 a = @Port3_NativeQueryBody.Ops.op5 b)
    (h6 : @Port3_NativeQueryBody.Ops.op6 a = @Port3_NativeQueryBody.Ops.op6 b)
    (h7 : @Port3_NativeQueryBody.Ops.op7 a = @Port3_NativeQueryBody.Ops.op7 b)
    (h8 : @Port3_NativeQueryBody.Ops.op8 a = @Port3_NativeQueryBody.Ops.op8 b)
    (h9 : @Port3_NativeQueryBody.Ops.op9 a = @Port3_NativeQueryBody.Ops.op9 b)
    (h10 : @Port3_NativeQueryBody.Ops.op10 a = @Port3_NativeQueryBody.Ops.op10 b)
    (h11 : @Port3_NativeQueryBody.Ops.op11 a = @Port3_NativeQueryBody.Ops.op11 b)
    (h12 : @Port3_NativeQueryBody.Ops.op12 a = @Port3_NativeQueryBody.Ops.op12 b)
    (h13 : @Port3_NativeQueryBody.Ops.op13 a = @Port3_NativeQueryBody.Ops.op13 b)
    (h14 : @Port3_NativeQueryBody.Ops.op14 a = @Port3_NativeQueryBody.Ops.op14 b)
    (h15 : @Port3_NativeQueryBody.Ops.op15 a = @Port3_NativeQueryBody.Ops.op15 b)
    (h16 : @Port3_NativeQueryBody.Ops.op16 a = @Port3_NativeQueryBody.Ops.op16 b)
    (h17 : @Port3_NativeQueryBody.Ops.op17 a = @Port3_NativeQueryBody.Ops.op17 b)
    (h18 : @Port3_NativeQueryBody.Ops.op18 a = @Port3_NativeQueryBody.Ops.op18 b)
    (h19 : @Port3_NativeQueryBody.Ops.op19 a = @Port3_NativeQueryBody.Ops.op19 b)
    (h20 : @Port3_NativeQueryBody.Ops.op20 a = @Port3_NativeQueryBody.Ops.op20 b)
    (h21 : @Port3_NativeQueryBody.Ops.op21 a = @Port3_NativeQueryBody.Ops.op21 b)
    (h22 : @Port3_NativeQueryBody.Ops.widePartialEq a = @Port3_NativeQueryBody.Ops.widePartialEq b)
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
  cases h9
  cases h10
  cases h11
  cases h12
  cases h13
  cases h14
  cases h15
  cases h16
  cases h17
  cases h18
  cases h19
  cases h20
  cases h21
  cases h22
  rfl
#print axioms query_ext
theorem query_op0 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op0 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op0 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op0
theorem query_op1 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op1 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op1 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op1
theorem query_op2 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op2 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op2 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op2
theorem query_op3 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op3 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op3 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op3
theorem query_op4 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op4 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op4 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op4
theorem query_op5 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op5 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op5 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op5
theorem query_op6 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op6 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op6 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op6
theorem query_op7 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op7 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op7 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op7
theorem query_op8 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op8 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op8 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op8
theorem query_op9 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op9 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op9 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op9
theorem query_op10 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op10 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op10 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op10
theorem query_op11 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op11 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op11 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op11
theorem query_op12 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op12 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op12 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op12
theorem query_op13 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op13 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op13 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op13
theorem query_op14 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op14 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op14 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op14
theorem query_op15 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op15 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op15 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op15
theorem query_op16 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op16 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op16 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op16
theorem query_op17 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op17 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op17 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op17
theorem query_op18 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op18 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op18 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op18
theorem query_op19 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op19 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op19 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op19
theorem query_op20 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op20 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op20 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op20
theorem query_op21 {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.op21 (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.op21 (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_op21
theorem query_widePartialEq {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    @Port3_NativeQueryBody.Ops.widePartialEq (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      @Port3_NativeQueryBody.Ops.widePartialEq (JHe_InstalledData.deployedConfiguration m err r).query := by
  rfl
#print axioms query_widePartialEq
theorem query {C : Type} (m : JHe_InstalledData.Uninstalled C) (err : C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err (JHe_InstalledData.deployedConfiguration m err r) r).query=
      (JHe_InstalledData.deployedConfiguration m err r).query := by
  exact query_ext _ _ (query_op0 m err r) (query_op1 m err r) (query_op2 m err r) (query_op3 m err r) (query_op4 m err r) (query_op5 m err r) (query_op6 m err r) (query_op7 m err r) (query_op8 m err r) (query_op9 m err r) (query_op10 m err r) (query_op11 m err r) (query_op12 m err r) (query_op13 m err r) (query_op14 m err r) (query_op15 m err r) (query_op16 m err r) (query_op17 m err r) (query_op18 m err r) (query_op19 m err r) (query_op20 m err r) (query_op21 m err r) (query_widePartialEq m err r)
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
