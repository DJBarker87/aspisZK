import R1Z.PV_CB_IsEmpty
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_VecDefault
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_IsEmpty.selected ops with op35 := ProverRwSuccessVectors.empty}
theorem op35_installed (ops : ExternalFuns) (T : Type) :
    (selected ops).op35 T = .ok (alloc.vec.Vec.new T) := rfl
#print axioms op35_installed
end R1Z.PV_CB_VecDefault
