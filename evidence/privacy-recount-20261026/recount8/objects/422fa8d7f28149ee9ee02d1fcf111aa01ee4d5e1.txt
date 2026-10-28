import R1Z.PV_CB_Op80Funs
import R1Z.PV_CB_Op80Transport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op80Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op80Transport
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op80 := fun inst x y h => PV_CB_ShippedOp80.phi (encode inst) x y h}
/-- Every callback and its Result is preserved by the bijective CodeField conversion. -/
theorem op80_source (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Array E 4#usize) :
    (selected ops).op80 inst x y h =
      PV_CB_ShippedOp80.aspis_core.r0.fold.phi_inverse (encode inst) x y h := rfl
#print axioms op80_source
end R1Z.PV_CB_Op80Exact
