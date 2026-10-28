import R1Z.PV_CB_Pop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_IsEmpty
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Pop.selected ops with op34 := ProverRwSuccessVectors.isEmpty}
theorem op34_installed (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (selected ops).op34 A v = .ok true ↔ v.val = [] := by
  change ProverRwSuccessVectors.isEmpty A v = .ok true ↔ _
  simp [ProverRwSuccessVectors.isEmpty]
#print axioms op34_installed
end R1Z.PV_CB_IsEmpty
