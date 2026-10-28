import R1Z.PV_CB_Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op109Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op109_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (PV_CB_Field.selected ops).op109 x =
      ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv x := rfl
#print axioms op109_source
end R1Z.PV_CB_Op109Source
