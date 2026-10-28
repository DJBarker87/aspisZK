import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op72Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Current72
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op72Transport
variable [ExternalTypes]
theorem op72_source (ops : ExternalFuns) (x : aspis_core.field.QM31) (bytes : Slice U8) :
    (ProverRwP6BodyStore.selected ops).op72 x bytes =
      PV_CB_ShippedOp72.aspis_core.field.QM31.write_le_bytes (encode x) bytes := by
  exact PV_CB_Op72Exact.op72_source ops x bytes
#print axioms op72_source
end R1Z.PV_Join_Current72
