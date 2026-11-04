import PV_B3P_TrailingEvents587227
namespace PV_B3P_TrailingIndices587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_TrailingEvents587227
set_option autoImplicit false
/-- Actual source nonzero-loop cttz observation at 397:95965c546ae80dd61779:30838. -/
theorem certificate_30838 {α : Type} (bits : BitVec 16) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent bits effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate bits effects observed ran normal first second
#print axioms certificate_30838
/-- Actual source nonzero-loop cttz observation at 397:95965c546ae80dd61779:30843. -/
theorem certificate_30843 {α : Type} (bits : BitVec 16) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent bits effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate bits effects observed ran normal first second
#print axioms certificate_30843
end PV_B3P_TrailingIndices587227
