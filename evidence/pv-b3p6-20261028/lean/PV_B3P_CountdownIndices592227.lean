import PV_B3P_CountdownEvents592227
namespace PV_B3P_CountdownIndices592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Checked source counter frame at 7:95965c546ae80dd61779:29218. -/
theorem certificate_0 {α : Type} (n : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_CountdownEvents592227.sourceEvent 24#usize 0 n effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_CountdownEvents592227.event_certificate 24#usize 0 n effects observed ran normal first second
#print axioms certificate_0
/-- Checked source counter frame at 7:95965c546ae80dd61779:29223. -/
theorem certificate_1 {α : Type} (n : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_CountdownEvents592227.sourceEvent 4#usize 0 n effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_CountdownEvents592227.event_certificate 4#usize 0 n effects observed ran normal first second
#print axioms certificate_1
/-- Checked source counter frame at 234:95965c546ae80dd61779:30396. -/
theorem certificate_2 {α : Type} (n : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_CountdownEvents592227.sourceEvent 9#usize 7 n effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_CountdownEvents592227.event_certificate 9#usize 7 n effects observed ran normal first second
#print axioms certificate_2
end PV_B3P_CountdownIndices592227
