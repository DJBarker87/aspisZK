import R1Z.PV_CB_Op100Funs
import R1Z.PV_CB_Op100Transport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op100Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op100Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op100 := fun x => do
    let y ← PV_CB_ShippedOp100.wide_neg (encodeW x)
    ok (decodeW y)}
theorem op100_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op100 x = (do
      let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg (encodeW x)
      ok (decodeW y)) := rfl
#print axioms op100_source
end R1Z.PV_CB_Op100Exact
