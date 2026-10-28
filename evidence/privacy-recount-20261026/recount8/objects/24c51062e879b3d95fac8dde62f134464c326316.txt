import R1Z.PV_CB_Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op105Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op105_source (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (PV_CB_Field.selected ops).op105 x =
      ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv x := rfl
#print axioms op105_source
end R1Z.PV_CB_Op105Source
