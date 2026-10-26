import R1Z.PV_CB_Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op107Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op107_source (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (PV_CB_Field.selected ops).op107 x =
      ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv x := rfl
#print axioms op107_source
end R1Z.PV_CB_Op107Source
