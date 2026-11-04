import PV_B3P_SliceMetadata581227
namespace PV_B3P_RangeSlice587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_SliceMetadata581227
set_option autoImplicit false
/-- Actual helper318 metadata, two reborrows and source assertion319:21975. -/
def sourceState (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent start 4#usize 16 0 effects
theorem certificate {α : Type} (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (decide (observed.index ≤ observed.length) = true) ∧
      branch (decide (observed.index ≤ observed.length) = true) normal first =
        branch (decide (observed.index ≤ observed.length) = true) normal second :=
  event_certificate start 4#usize 16 0 effects observed ran normal first second
#print axioms certificate
end PV_B3P_RangeSlice587227
