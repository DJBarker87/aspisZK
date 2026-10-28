import R1Z.PV_CB_Op109Funs
import R1Z.PV_CB_Op109Transport
/-! PREPARED: fresh candidate extraction and type-check still required.
The older PV_CB_Op109Source.op109_source interface is retained unchanged. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op109Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op109Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op109 := fun x => do
    let value ← PV_CB_ShippedOp109.wide_inv (encodeW x)
    ok (value.map decodeW)}
/-- Complete Result and Option, for every raw field input. -/
theorem op109_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op109 x = (do
      let value ← PV_CB_ShippedOp109.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv (encodeW x)
      ok (value.map decodeW)) := rfl
#print axioms op109_source
end R1Z.PV_CB_Op109Exact
