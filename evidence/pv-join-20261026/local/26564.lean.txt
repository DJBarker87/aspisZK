import R1Z.PV_CB_Op101Funs
import R1Z.PV_CB_Op101Transport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op101Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op101Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op101 := fun x => do
    let y ← PV_CB_ShippedOp101.qm_neg (encode x)
    ok (decode y)}
theorem op101_source (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (selected ops).op101 x = (do
      let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg (encode x)
      ok (decode y)) := rfl
#print axioms op101_source
end R1Z.PV_CB_Op101Exact
