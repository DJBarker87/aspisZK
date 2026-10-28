import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
namespace R1Z.PV_ScaleUpdate
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
theorem preserve (ops : ExternalFuns)
    (scale : aspis_core.field.QM31 → U32 → Result aspis_core.field.QM31)
    (same : scale=ops.op70) : {ops with op70 := scale}=ops := by
  cases same
  rfl
#print axioms preserve
end R1Z.PV_ScaleUpdate
