import R1Z.PV_CB_Op71Funs
import R1Z.PV_CB_Op71Transport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op71Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op71Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op71 := fun bytes => do
    let value ← PV_CB_ShippedOp71.qm_parse bytes
    ok (value.map decode)}
/-- Current shipped parser extraction, with a bijective nominal carrier conversion.
    Panic/failure, None, and Some outcomes remain distinct. -/
theorem op71_source (ops : ExternalFuns) (bytes : Slice U8) :
    (selected ops).op71 bytes = (do
      let value ← PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes bytes
      ok (value.map decode)) := rfl
#print axioms op71_source
end R1Z.PV_CB_Op71Exact
