import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op80Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Current80
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op80Transport
variable [ExternalTypes]
theorem op80_source (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Array E 4#usize) :
    (ProverRwP6BodyStore.selected ops).op80 inst x y h =
      PV_CB_ShippedOp80.aspis_core.r0.fold.phi_inverse (encode inst) x y h := by
  exact PV_CB_Op80Exact.op80_source ops inst x y h
#print axioms op80_source
end R1Z.PV_Join_Current80
