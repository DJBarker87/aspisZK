import R1Z.PV_CB_Codecs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_PointClone
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Codecs.selected ops with op77 := ProverRwSuccessGeneric.pointClone}
theorem op77_installed (ops : ExternalFuns) {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E) :
    (selected ops).op77 inst p = (do
      let x ← inst.clone p.x
      let y ← inst.clone p.y
      .ok ⟨x,y⟩) := rfl
#print axioms op77_installed
end R1Z.PV_CB_PointClone
