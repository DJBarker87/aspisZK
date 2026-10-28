import R1Z.PV_CB_VecDefault
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_VecArray
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_VecDefault.selected ops with op36 := ProverRwSuccessVectors.toArray}
theorem op36_accept (ops : ExternalFuns) {T : Type} (A : Type) (N : Usize)
    (v : alloc.vec.Vec T) (h : v.val.length = N.val) :
    (selected ops).op36 A N v = .ok (.Ok ⟨v.val,h⟩) := by
  change ProverRwSuccessVectors.toArray A N v = _
  simp only [ProverRwSuccessVectors.toArray,dif_pos h]
theorem op36_reject (ops : ExternalFuns) {T : Type} (A : Type) (N : Usize)
    (v : alloc.vec.Vec T) (h : v.val.length ≠ N.val) :
    (selected ops).op36 A N v = .ok (.Err v) := by
  change ProverRwSuccessVectors.toArray A N v = _
  simp only [ProverRwSuccessVectors.toArray,dif_neg h]
#print axioms op36_accept
#print axioms op36_reject
end R1Z.PV_CB_VecArray
