import NLA_LaneStep
set_option autoImplicit false
noncomputable section
namespace NLA_AllocationPrefix
open Aeneas Aeneas.Std Result
abbrev PE := NKF_BoxModel.PE
/-- Partial allocation outcome supplied at the actual allocation site. This
support definition preserves fail/div; it is not an allocator realization. -/
def allocate {A : Type} (action : Result Unit)
 (value : core.result.Result A PE) : Result (core.result.Result A PE) :=
 match value with
 | .Err e => ok (.Err e)
 | .Ok value => do
   let _ ← action
   ok (.Ok value)

theorem prior_error {A : Type} (action : Result Unit) (e : PE) :
 @allocate A action (.Err e) = ok (.Err e) := rfl

theorem returned {A : Type} (value : A) :
 allocate (ok ()) (.Ok value) = ok (.Ok value) := rfl

theorem abort {A : Type} (value : A) (e : Error) :
 allocate (.fail e) (.Ok value) = .fail e := rfl

theorem divergence {A : Type} (value : A) :
 allocate .div (.Ok value) = .div := rfl

/-- Counterexample to treating an unused Reservation plus a value identity
as the allocation law: the actual partial outcome matters on the Ok arm. -/
theorem failure_is_not_success {A : Type} (value : A) (e : Error) :
 allocate (.fail e) (.Ok value) ≠ allocate (ok ()) (.Ok value) := by
 simp only [abort,returned]
 intro h
 cases h

#print axioms prior_error
#print axioms returned
#print axioms abort
#print axioms divergence
#print axioms failure_is_not_success
end NLA_AllocationPrefix
