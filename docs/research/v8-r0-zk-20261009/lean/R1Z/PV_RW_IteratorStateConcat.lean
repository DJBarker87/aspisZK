import R1Z.PV_RW_IteratorStateLoop
import R1Z.PV_RW_NativeForConcat
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_IteratorStateConcat
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
abbrev Iter := PV_RW_IteratorStateLoop.Iter
variable [ExternalTypes]

theorem split (ops : ExternalFuns) (lambda : Q) (left right joined : Slice U32)
    (shape : joined.val=left.val++right.val) (state : Q × Q) :
    PV_RW_IteratorStateLoop.run ops lambda (⟨joined,0⟩ : Iter) state=(do
      let middle ← PV_RW_IteratorStateLoop.run ops lambda (⟨left,0⟩ : Iter) state
      PV_RW_IteratorStateLoop.run ops lambda (⟨right,0⟩ : Iter) middle) := by
  simp only [PV_RW_IteratorStateLoop.control]
  exact PV_RW_NativeForConcat.split _ left right joined shape state
#print axioms split
end R1Z.PV_RW_IteratorStateConcat
