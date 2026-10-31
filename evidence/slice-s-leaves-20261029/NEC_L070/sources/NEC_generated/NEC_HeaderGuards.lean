import NEC_HeaderPredicates
set_option autoImplicit false
namespace NEC_HeaderGuards
open Aeneas Aeneas.Std Result

/-- Fold one symbolic zero/equality guard; no enumeration of all byte paths. -/
theorem guarded (condition : Prop) [Decidable condition] (next : Bool) :
 (if condition then (Result.ok next : Result Bool) else Result.ok false)=
 Result.ok (decide condition && next) := by
 by_cases h : condition <;> simp [h]

#print axioms guarded
end NEC_HeaderGuards
