import PV_B3P_DominatedEvents578227
namespace PV_B3P_MetadataIndices584227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_DominatedEvents578227
set_option autoImplicit false
/-- Instance 224:95965c546ae80dd61779, statement 30106; all incoming metadata is bound. -/
def sourceState_0 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 7 0 index effects
theorem certificate_0 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 7 0 index effects observed ran normal first second
#print axioms certificate_0
/-- Instance 224:95965c546ae80dd61779, statement 30111; all incoming metadata is bound. -/
def sourceState_1 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 7 0 index effects
theorem certificate_1 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_1 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 7 0 index effects observed ran normal first second
#print axioms certificate_1
/-- Instance 241:95965c546ae80dd61779, statement 30479; all incoming metadata is bound. -/
def sourceState_2 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_2 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_2 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_2
/-- Instance 241:95965c546ae80dd61779, statement 30484; all incoming metadata is bound. -/
def sourceState_3 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_3 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_3 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_3
end PV_B3P_MetadataIndices584227
