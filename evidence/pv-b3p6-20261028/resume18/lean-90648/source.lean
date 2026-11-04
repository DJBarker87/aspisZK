import PV_B3P_MinRangeEvents587227
namespace PV_B3P_MinRangeIndices587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_MinRangeEvents587227
set_option autoImplicit false
/-- Source min/cursor/metadata projection at 224:95965c546ae80dd61779:30036. -/
def sourceState_0 (handler : Str → Result Never) (start candidate : Usize)
    (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent handler start candidate 7#usize 0 effects
theorem certificate_0 {α : Type} (handler : Str → Result Never) (start candidate : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_0 handler start candidate effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler start candidate 7#usize 0 effects observed ran normal first second
#print axioms certificate_0
/-- Source min/cursor/metadata projection at 224:95965c546ae80dd61779:30041. -/
def sourceState_1 (handler : Str → Result Never) (start candidate : Usize)
    (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent handler start candidate 7#usize 0 effects
theorem certificate_1 {α : Type} (handler : Str → Result Never) (start candidate : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_1 handler start candidate effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler start candidate 7#usize 0 effects observed ran normal first second
#print axioms certificate_1
end PV_B3P_MinRangeIndices587227
