import PV_B3P_DominatedEvents578227
namespace PV_B3P_DominatedIndices578227_01
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_DominatedEvents578227
set_option autoImplicit false
/-- Instance 362:95965c546ae80dd61779, instruction 30781, strict test 24311. -/
def sourceState_24 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_24 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_24 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_24
/-- Instance 362:95965c546ae80dd61779, instruction 30786, strict test 24311. -/
def sourceState_25 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_25 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_25 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_25
/-- Instance 362:95965c546ae80dd61779, instruction 30791, strict test 24311. -/
def sourceState_26 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_26 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_26 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_26
/-- Instance 373:95965c546ae80dd61779, instruction 30828, strict test 25106. -/
def sourceState_27 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_27 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_27 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_27
/-- Instance 373:95965c546ae80dd61779, instruction 30833, strict test 25106. -/
def sourceState_28 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_28 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_28 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_28
/-- Instance 494:95965c546ae80dd61779, instruction 30953, strict test 27289. -/
def sourceState_29 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_29 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_29 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_29
end PV_B3P_DominatedIndices578227_01
