import R1Z.PV_CB_Take
import R1Z.ProverRwSuccessVectors
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Pop
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Take.selected ops with op33 := ProverRwSuccessVectors.pop}
theorem op33_installed (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    ∃ tail, (selected ops).op33 A v = .ok (v.val.getLast?,tail) ∧
      tail.val = v.val.dropLast := ⟨_,rfl,rfl⟩
theorem op33_empty (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T)
    (h : v.val = []) :
    ∃ tail, (selected ops).op33 A v = .ok (none,tail) ∧ tail.val = [] := by
  obtain ⟨tail, reply, value⟩ := op33_installed ops A v
  refine ⟨tail, ?_, ?_⟩
  · simpa [h] using reply
  · simpa [h] using value
#print axioms op33_installed
#print axioms op33_empty
end R1Z.PV_CB_Pop
