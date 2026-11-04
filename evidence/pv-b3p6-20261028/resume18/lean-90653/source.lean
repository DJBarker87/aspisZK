import PV_B3P_ArithmeticEvents583227
import PV_B3P_FourWayEvents587227
namespace PV_B3P_CaptureGuards587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Captured source outer column at 524:95965c546ae80dd61779:31238. -/
def sourceState_0 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.bounded input0 4) 12 effects
theorem certificate_0 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 input0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.bounded input0 4) 12 effects observed ran normal first second
#print axioms certificate_0
/-- Captured source outer column at 524:95965c546ae80dd61779:31248. -/
def sourceState_1 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 8 effects
theorem certificate_1 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_1 input0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 8 effects observed ran normal first second
#print axioms certificate_1
/-- Captured source outer column at 524:95965c546ae80dd61779:31258. -/
def sourceState_2 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 8) (.bounded input0 4) (UScalar.size .Usize)) 4 effects
theorem certificate_2 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_2 input0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.literal 8) (.bounded input0 4) (UScalar.size .Usize)) 4 effects observed ran normal first second
#print axioms certificate_2
/-- Captured source outer column at 524:95965c546ae80dd61779:31268. -/
def sourceState_3 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 12) (.bounded input0 4) (UScalar.size .Usize)) 0 effects
theorem certificate_3 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_3 input0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.literal 12) (.bounded input0 4) (UScalar.size .Usize)) 0 effects observed ran normal first second
#print axioms certificate_3
/-- Actual four-arm source match at 428:95965c546ae80dd61779:26180. -/
def sourceState_panic_428 (column : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 4 0 column effects
theorem panic_428 {α : Type} (column : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_panic_428 column effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (PV_B3P_FourWayEvents587227.sourceCondition observed = true) ∧
      branch (PV_B3P_FourWayEvents587227.sourceCondition observed = true) normal first =
        branch (PV_B3P_FourWayEvents587227.sourceCondition observed = true) normal second :=
  PV_B3P_FourWayEvents587227.event_certificate column effects observed ran normal first second
#print axioms panic_428
/-- Actual four-arm source match at 536:95965c546ae80dd61779:29118. -/
def sourceState_panic_536 (column : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 4 0 column effects
theorem panic_536 {α : Type} (column : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_panic_536 column effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (PV_B3P_FourWayEvents587227.sourceCondition observed = true) ∧
      branch (PV_B3P_FourWayEvents587227.sourceCondition observed = true) normal first =
        branch (PV_B3P_FourWayEvents587227.sourceCondition observed = true) normal second :=
  PV_B3P_FourWayEvents587227.event_certificate column effects observed ran normal first second
#print axioms panic_536
end PV_B3P_CaptureGuards587227
