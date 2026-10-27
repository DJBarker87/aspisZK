import R1Z.PV_CB_Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op101Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op101_source (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (PV_CB_Field.selected ops).op101 x =
      ProverRwSuccessInverseSource.field.QM31.neg x := rfl
#print axioms op101_source
end R1Z.PV_CB_Op101Source
