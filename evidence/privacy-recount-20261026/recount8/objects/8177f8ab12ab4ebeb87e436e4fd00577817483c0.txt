import Aeneas
import R1Z.PV_RW_Outcome
set_option autoImplicit false
namespace R1Z.PV_RW_ResultOutcome
open Aeneas Aeneas.Std

def toOutcome {A : Type} : Result A → PV_RW_Outcome.Outcome Error A
  | .ok value => .ok value
  | .fail error => .fail error
  | .div => .div

def fromOutcome {A : Type} : PV_RW_Outcome.Outcome Error A → Result A
  | .ok value => .ok value
  | .fail error => .fail error
  | .div => .div

theorem roundtrip {A : Type} (result : Result A) : fromOutcome (toOutcome result)=result := by
  cases result <;> rfl

theorem outcome_roundtrip {A : Type} (result : PV_RW_Outcome.Outcome Error A) :
    toOutcome (fromOutcome result)=result := by
  cases result <;> rfl

theorem bind {A B : Type} (result : Result A) (next : A → Result B) :
    toOutcome (result >>= next)=
      PV_RW_Outcome.bind (toOutcome result) (fun value => toOutcome (next value)) := by
  cases result <;> rfl

theorem injective {A : Type} (left right : Result A) (same : toOutcome left=toOutcome right) :
    left=right := by
  calc
    left=fromOutcome (toOutcome left) := (roundtrip left).symm
    _=fromOutcome (toOutcome right) := congrArg fromOutcome same
    _=right := roundtrip right

theorem equal_iff {A : Type} (left right : Result A) :
    toOutcome left=toOutcome right ↔ left=right := by
  constructor
  · exact injective left right
  · exact congrArg toOutcome
#print axioms roundtrip
#print axioms outcome_roundtrip
#print axioms bind
#print axioms injective
#print axioms equal_iff
end R1Z.PV_RW_ResultOutcome
