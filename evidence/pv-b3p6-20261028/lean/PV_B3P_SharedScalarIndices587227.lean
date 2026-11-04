import PV_B3P_RangeEvents578227
namespace PV_B3P_SharedScalarIndices587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Actual typed shared scalar frame at 218:95965c546ae80dd61779:29807. -/
def sourceState_0 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_0 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_0
/-- Actual typed shared scalar frame at 362:95965c546ae80dd61779:30806. -/
def sourceState_1 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_1 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_1 handler start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_1
end PV_B3P_SharedScalarIndices587227
