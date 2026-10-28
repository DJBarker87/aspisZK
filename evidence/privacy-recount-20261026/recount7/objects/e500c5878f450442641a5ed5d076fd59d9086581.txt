import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op100Source
import R1Z.PV_CB_Op101Source
import R1Z.PV_CB_Op105Source
import R1Z.PV_CB_Op107Source
import R1Z.PV_CB_Op109Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Field
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected
theorem op100_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op100 x =
      ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg x := by
  exact PV_CB_Op100Source.op100_source ops x
#print axioms op100_source
theorem op101_source (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (selected ops).op101 x =
      ProverRwSuccessInverseSource.field.QM31.neg x := by
  exact PV_CB_Op101Source.op101_source ops x
#print axioms op101_source
theorem op105_source (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (selected ops).op105 x =
      ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv x := by
  exact PV_CB_Op105Source.op105_source ops x
#print axioms op105_source
theorem op107_source (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (selected ops).op107 x =
      ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv x := by
  exact PV_CB_Op107Source.op107_source ops x
#print axioms op107_source
theorem op109_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op109 x =
      ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv x := by
  exact PV_CB_Op109Source.op109_source ops x
#print axioms op109_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_Field
