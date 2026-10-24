import Port23PUSH_Frame
set_option autoImplicit false
noncomputable section
namespace Port23PUSH
open Aeneas Aeneas.Std Result

/-- Derived from the actual source-emitted outer mutable frame, including the
live Vec setter. The missing array primitive remains an explicit parameter. -/
theorem push_terms_length (arrayIntoIter : ArrayIntoIter)
    (b after : verifier.BatchedWeights) (index : Usize) (power : field.QM31) (basis : field.M31)
    (run : verifier.BatchedWeights.push arrayIntoIter b index power basis = ok after) :
    after.terms = b.terms ∧ after.raw.val.length = b.raw.val.length := by
  obtain ⟨row,updated,hr,hu,frame⟩ := push_success_frame arrayIntoIter b after index power basis run
  subst after
  exact ⟨rfl,by simp [alloc.vec.Vec.set]⟩

#print axioms push_terms_length
end Port23PUSH
end
