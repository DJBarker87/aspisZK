import PV_B3P_StepSource572227
namespace PV_B3P_StepFamily572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Exact source instance 186:763ba5cae8a1b6e6a5de; observe current fields at the guarded call. -/
def range_state (r : core.ops.range.Range Usize) : Result (Option (Option Usize)) :=
  PV_B3P_StepSource572227.event r.start r.end

theorem range_guard (r : core.ops.range.Range Usize) (answer : Option Usize)
    (observed : range_state r = .ok (some answer)) : optionGuard answer :=
  PV_B3P_StepSource572227.event_guard r.start r.end answer observed

theorem range_certificate {α : Type} (r : core.ops.range.Range Usize) (answer : Option Usize)
    (observed : range_state r = .ok (some answer))
    (normal first second : Result α) :
    ¬ diagnostic (optionGuard answer) ∧
      branch (optionGuard answer) normal first = branch (optionGuard answer) normal second :=
  PV_B3P_StepSource572227.event_certificate r.start r.end answer observed normal first second
#print axioms range_guard
#print axioms range_certificate
/-- Exact source instance 337:763ba5cae8a1b6e6a5de; observe current fields at the guarded call. -/
def inclusive_next_state (r : core.ops.range.RangeInclusive Usize) : Result (Option (Option Usize)) :=
  PV_B3P_StepSource572227.event r.start r.end

theorem inclusive_next_guard (r : core.ops.range.RangeInclusive Usize) (answer : Option Usize)
    (observed : inclusive_next_state r = .ok (some answer)) : optionGuard answer :=
  PV_B3P_StepSource572227.event_guard r.start r.end answer observed

theorem inclusive_next_certificate {α : Type} (r : core.ops.range.RangeInclusive Usize) (answer : Option Usize)
    (observed : inclusive_next_state r = .ok (some answer))
    (normal first second : Result α) :
    ¬ diagnostic (optionGuard answer) ∧
      branch (optionGuard answer) normal first = branch (optionGuard answer) normal second :=
  PV_B3P_StepSource572227.event_certificate r.start r.end answer observed normal first second
#print axioms inclusive_next_guard
#print axioms inclusive_next_certificate
/-- Exact source instance 217:218cbedca9a6d864b53a; observe current fields at the guarded call. -/
def inclusive_fold_state (r : core.ops.range.RangeInclusive Usize) : Result (Option (Option Usize)) :=
  PV_B3P_StepSource572227.event r.start r.end

theorem inclusive_fold_guard (r : core.ops.range.RangeInclusive Usize) (answer : Option Usize)
    (observed : inclusive_fold_state r = .ok (some answer)) : optionGuard answer :=
  PV_B3P_StepSource572227.event_guard r.start r.end answer observed

theorem inclusive_fold_certificate {α : Type} (r : core.ops.range.RangeInclusive Usize) (answer : Option Usize)
    (observed : inclusive_fold_state r = .ok (some answer))
    (normal first second : Result α) :
    ¬ diagnostic (optionGuard answer) ∧
      branch (optionGuard answer) normal first = branch (optionGuard answer) normal second :=
  PV_B3P_StepSource572227.event_certificate r.start r.end answer observed normal first second
#print axioms inclusive_fold_guard
#print axioms inclusive_fold_certificate
end PV_B3P_StepFamily572227
