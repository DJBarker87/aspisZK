import R1Z.PDict_RejectionStd
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RejectValues
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_RejectionStd.native
abbrev selected := PDict_RejectionStd.selected
variable (base : ExternalTypes) (ops : @ExternalFuns (native base))

theorem absent_predicate {T C : Type} (callback : core.ops.function.FnOnce C T Bool)
    (state : C) :
    (selected base ops).op5 callback none state = .ok false := rfl

theorem present_predicate {T C : Type} (callback : core.ops.function.FnOnce C T Bool)
    (state : C) (value : T) :
    (selected base ops).op5 callback (some value) state =
      callback.call_once state value := rfl

theorem borrowed_option {T : Type} (value : Option T) :
    (selected base ops).op6 value = .ok value := by cases value <;> rfl

theorem absent_error {T E : Type} (error : E) :
    (selected base ops).op7 (none : Option T) error = .ok (.Err error) := rfl

theorem present_value {T E : Type} (value : T) (error : E) :
    (selected base ops).op7 (some value) error = .ok (.Ok value) := rfl

theorem absent_branch {T : Type} :
    (selected base ops).op9 (none : Option T) = .ok (.Break none) := rfl

theorem present_branch {T : Type} (value : T) :
    (selected base ops).op9 (some value) = .ok (.Continue value) := rfl

theorem error_map {T E U C : Type} (callback : core.ops.function.FnOnce C T U)
    (error : E) (state : C) :
    (selected base ops).op11 callback (.Err error) state = .ok (.Err error) := rfl

theorem success_map {T E U C : Type} (callback : core.ops.function.FnOnce C T U)
    (value : T) (state : C) :
    (selected base ops).op11 callback (.Ok value : core.result.Result T E) state =
      (do let out ← callback.call_once state value; .ok (.Ok out)) := rfl

#print axioms absent_predicate
#print axioms present_predicate
#print axioms borrowed_option
#print axioms absent_error
#print axioms present_value
#print axioms absent_branch
#print axioms present_branch
#print axioms error_map
#print axioms success_map
end R1Z.PDict_RejectValues
