import PV_B3P_ArithmeticEvents583227
import PV_B3P_RangeEvents578227
namespace PV_B3P_ComputedIndices583227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Instance 1:95965c546ae80dd61779, scalar event 29177. -/
def sourceState_0 (input : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.quotient (.bounded input 84) 28) 0 effects
theorem certificate_0 {α : Type} (input : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.quotient (.bounded input 84) 28) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.quotient (.bounded input 84) 28) 0 effects observed ran normal first second
#print axioms certificate_0
/-- Instance 1:95965c546ae80dd61779, scalar event 29182. -/
def sourceState_1 (input : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.remainder input 28) 1 effects
theorem certificate_1 {α : Type} (input : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.remainder input 28) 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.remainder input 28) 1 effects observed ran normal first second
#print axioms certificate_1
/-- Instance 9:95965c546ae80dd61779, scalar event 29229. -/
def sourceState_2 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 10 0 index effects
theorem certificate_2 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 10 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 10 0 index effects observed ran normal first second
#print axioms certificate_2
/-- Instance 9:95965c546ae80dd61779, scalar event 29234. -/
def sourceState_3 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 10 0 index effects
theorem certificate_3 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 10 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 10 0 index effects observed ran normal first second
#print axioms certificate_3
/-- Instance 14:95965c546ae80dd61779, scalar event 29249. -/
def sourceState_4 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,20#usize⟩ 0 effects
theorem certificate_4 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,20#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,20#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_4
/-- Instance 14:95965c546ae80dd61779, scalar event 29254. -/
def sourceState_5 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,20#usize⟩ 0 effects
theorem certificate_5 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,20#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,20#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_5
/-- Instance 61:95965c546ae80dd61779, scalar event 29604. -/
def sourceState_6 (input : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input 15) 0 effects
theorem certificate_6 {α : Type} (input : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input 15) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.bitAnd input 15) 0 effects observed ran normal first second
#print axioms certificate_6
/-- Instance 432:95965c546ae80dd61779, scalar event 30908. -/
def sourceState_7 (input : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input 3) 0 effects
theorem certificate_7 {α : Type} (input : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input 3) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.bitAnd input 3) 0 effects observed ran normal first second
#print axioms certificate_7
end PV_B3P_ComputedIndices583227
