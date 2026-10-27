import RPz7_ClaimsUnrolledFinish
/-! Safe owned-reference std interpretation. The reserve result is the existing
allocator outcome, not an assumption of successful Claims. This module proves
value content laws only; P6 must connect shipped unsafe construction to this
reference before any native ledger row can be removed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_StdModel
open Aeneas Aeneas.Std Result
abbrev ReserveError := AspisR1ClaimsUnrolledParent.alloc.collections.TryReserveError
abbrev Reservation := core.result.Result Unit ReserveError

def calls (reservation : Reservation) : ClaimsUnrolledFinish.StdCalls where
  reserve := fun _ before _ => ok (reservation,before)
  intoBox := fun _ before => ok before.deref

theorem reserve_contents (reservation : Reservation) {T : Type} (A : Type)
    (before : alloc.vec.Vec T) (n : Usize) (result : Reservation)
    (after : alloc.vec.Vec T)
    (returned : (calls reservation).reserve A before n = ok (result,after)) :
    after = before ∧ result = reservation := by
  cases returned
  exact ⟨rfl,rfl⟩

theorem box_contents (reservation : Reservation) {T : Type} (A : Type)
    (before : alloc.vec.Vec T) (after : Slice T)
    (returned : (calls reservation).intoBox A before = ok after) :
    after.val = before.val := by
  cases returned
  rfl

theorem returning_nonvacuity {T : Type} (A : Type) (before : alloc.vec.Vec T)
    (n : Usize) :
    (calls (.Ok ())).reserve A before n = ok (.Ok (),before) ∧
    (calls (.Ok ())).intoBox A before = ok before.deref := ⟨rfl,rfl⟩

theorem error_contents (error : ReserveError) {T : Type} (A : Type)
    (before : alloc.vec.Vec T) (n : Usize) :
    (calls (.Err error)).reserve A before n = ok (.Err error,before) := rfl

#print axioms reserve_contents
#print axioms box_contents
#print axioms returning_nonvacuity
#print axioms error_contents
end AspisR1.NP6_StdModel
end
