import R1Z.PV_CB_PointClone
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Phi
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_PointClone.selected ops with
    op80 := ProverRwSuccessPhiSource.generic54.phi_inverse}
theorem op80_installed (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Array E 4#usize) :
    (selected ops).op80 inst x y h =
      ProverRwSuccessPhiSource.generic54.phi_inverse inst x y h := rfl
#print axioms op80_installed
end R1Z.PV_CB_Phi
