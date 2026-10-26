import R1Z.PV_CB_Phi
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op80Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op80_source (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Array E 4#usize) :
    (PV_CB_Phi.selected ops).op80 inst x y h =
      ProverRwSuccessPhiSource.generic54.phi_inverse inst x y h := rfl
#print axioms op80_source
end R1Z.PV_CB_Op80Source
