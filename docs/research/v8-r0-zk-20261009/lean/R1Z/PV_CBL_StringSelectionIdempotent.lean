import R1Z.PV_CBL_CallbackBundle
namespace R1Z.PV_CBL_StringSelectionIdempotent
open ProverRwFull
set_option autoImplicit false
noncomputable section
theorem installed (b : ExternalTypes) (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes b)) :
    PV_CBL_CallbackBundle.selectedString b (PV_CBL_CallbackBundle.selectedString b ops) =
      PV_CBL_CallbackBundle.selectedString b ops := rfl
#print axioms installed
end
end R1Z.PV_CBL_StringSelectionIdempotent
