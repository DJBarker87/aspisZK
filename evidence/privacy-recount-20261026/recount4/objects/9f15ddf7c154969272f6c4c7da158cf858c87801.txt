import R1Z.PV_CB_Op118Funs
import R1Z.PV_CB_Op118Arrays
/-! PREPARED: fresh extraction, array carrier transport and type-check required.
The older PV_CB_Op118Source.op118_source interface is retained unchanged. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op118Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op118Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op118 := fun x => do
    let value ← PV_CB_ShippedOp118.statement_points (encodeArray x)
    ok (decodePoints value)}
theorem op118_source (ops : ExternalFuns) (x : Array aspis_core.field.QM31 10#usize) :
    (selected ops).op118 x = (do
      let value ← PV_CB_ShippedOp118.aspis_core.state_only_prefix.r0.statement_points (encodeArray x)
      ok (decodePoints value)) := rfl
#print axioms op118_source
end R1Z.PV_CB_Op118Exact
