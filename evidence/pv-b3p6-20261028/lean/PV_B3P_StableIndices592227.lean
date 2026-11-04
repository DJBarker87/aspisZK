import PV_B3P_ArithmeticEvents583227
namespace PV_B3P_StableIndices592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Exact source 4*outer+inner at 218:95965c546ae80dd61779:29777. -/
def sourceState_0 (input0 input1 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.bounded input1 4) (UScalar.size .Usize)) 0 effects
theorem certificate_0 {α : Type} (input0 input1 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 input0 input1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.bounded input1 4) (UScalar.size .Usize)) 0 effects observed ran normal first second
#print axioms certificate_0
end PV_B3P_StableIndices592227
