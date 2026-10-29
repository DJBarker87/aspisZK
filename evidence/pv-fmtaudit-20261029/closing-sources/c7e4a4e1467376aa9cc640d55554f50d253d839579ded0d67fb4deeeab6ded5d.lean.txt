import R1Z.PV_CB_Op72Funs
import R1Z.PV_CB_Op72Transport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op72Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op72Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op72 := fun x bytes => PV_CB_ShippedOp72.qm_write (encode x) bytes}
/-- Sequential bounds checks and mutation-back closures are retained in the extraction. -/
theorem op72_source (ops : ExternalFuns) (x : aspis_core.field.QM31) (bytes : Slice U8) :
    (selected ops).op72 x bytes =
      PV_CB_ShippedOp72.aspis_core.field.QM31.write_le_bytes (encode x) bytes := rfl
#print axioms op72_source
end R1Z.PV_CB_Op72Exact
