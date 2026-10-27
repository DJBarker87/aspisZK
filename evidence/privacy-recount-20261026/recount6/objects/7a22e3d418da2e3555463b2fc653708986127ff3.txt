import R1Z.PV_CB_Op107Funs
import R1Z.PV_CB_Op107Transport
/-! PREPARED: fresh candidate extraction and type-check still required.
The older PV_CB_Op107Source.op107_source interface is retained unchanged. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op107Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op107Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op107 := fun x => do
    let value ← PV_CB_ShippedOp107.qm_inv (encode x)
    ok (value.map decode)}
/-- Complete Result and Option, for every raw field input. -/
theorem op107_source (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (selected ops).op107 x = (do
      let value ← PV_CB_ShippedOp107.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv (encode x)
      ok (value.map decode)) := rfl
#print axioms op107_source
end R1Z.PV_CB_Op107Exact
