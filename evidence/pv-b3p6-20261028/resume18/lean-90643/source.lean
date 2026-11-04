import PV_B3P_ArithmeticEvents583227
import PV_B3P_RangeEvents578227
namespace PV_B3P_ComputedIndices583227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Instance 1:95965c546ae80dd61779, scalar event 29177. -/
def sourceState_0 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.quotient (.bounded input0 84) 28) 0 effects
theorem certificate_0 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.quotient (.bounded input0 84) 28) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.quotient (.bounded input0 84) 28) 0 effects observed ran normal first second
#print axioms certificate_0
/-- Instance 1:95965c546ae80dd61779, scalar event 29182. -/
def sourceState_1 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.remainder input0 28) 1 effects
theorem certificate_1 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.remainder input0 28) 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.remainder input0 28) 1 effects observed ran normal first second
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
/-- Instance 56:95965c546ae80dd61779, scalar event 29476. -/
def sourceState_6 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 10) (.bounded input0 10) (UScalar.size .Usize)) 13 effects
theorem certificate_6 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 10) (.bounded input0 10) (UScalar.size .Usize)) 13 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.literal 10) (.bounded input0 10) (UScalar.size .Usize)) 13 effects observed ran normal first second
#print axioms certificate_6
/-- Instance 56:95965c546ae80dd61779, scalar event 29491. -/
def sourceState_7 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 20) (.bounded input0 10) (UScalar.size .Usize)) 3 effects
theorem certificate_7 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 20) (.bounded input0 10) (UScalar.size .Usize)) 3 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.literal 20) (.bounded input0 10) (UScalar.size .Usize)) 3 effects observed ran normal first second
#print axioms certificate_7
/-- Instance 61:95965c546ae80dd61779, scalar event 29604. -/
def sourceState_8 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input0 15) 0 effects
theorem certificate_8 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input0 15) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.bitAnd input0 15) 0 effects observed ran normal first second
#print axioms certificate_8
/-- Instance 218:95965c546ae80dd61779, scalar event 29782. -/
def sourceState_9 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 3 effects
theorem certificate_9 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 3 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 3 effects observed ran normal first second
#print axioms certificate_9
/-- Instance 218:95965c546ae80dd61779, scalar event 29787. -/
def sourceState_10 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 1) (UScalar.size .Usize)) 2 effects
theorem certificate_10 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 1) (UScalar.size .Usize)) 2 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 1) (UScalar.size .Usize)) 2 effects observed ran normal first second
#print axioms certificate_10
/-- Instance 218:95965c546ae80dd61779, scalar event 29792. -/
def sourceState_11 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 2) (UScalar.size .Usize)) 1 effects
theorem certificate_11 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 2) (UScalar.size .Usize)) 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 2) (UScalar.size .Usize)) 1 effects observed ran normal first second
#print axioms certificate_11
/-- Instance 218:95965c546ae80dd61779, scalar event 29797. -/
def sourceState_12 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 3) (UScalar.size .Usize)) 0 effects
theorem certificate_12 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 3) (UScalar.size .Usize)) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 3) (UScalar.size .Usize)) 0 effects observed ran normal first second
#print axioms certificate_12
/-- Instance 231:95965c546ae80dd61779, scalar event 30295. -/
def sourceState_13  (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 8) (.literal 1) (UScalar.size .Usize)) 6 effects
theorem certificate_13 {α : Type}  (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 8) (.literal 1) (UScalar.size .Usize)) 6 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.literal 8) (.literal 1) (UScalar.size .Usize)) 6 effects observed ran normal first second
#print axioms certificate_13
/-- Instance 231:95965c546ae80dd61779, scalar event 30305. -/
def sourceState_14  (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 8) (.literal 1) (UScalar.size .Usize)) 6 effects
theorem certificate_14 {α : Type}  (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.literal 8) (.literal 1) (UScalar.size .Usize)) 6 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.literal 8) (.literal 1) (UScalar.size .Usize)) 6 effects observed ran normal first second
#print axioms certificate_14
/-- Instance 346:95965c546ae80dd61779, scalar event 30720. -/
def sourceState_15 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 3 effects
theorem certificate_15 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 3 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) 3 effects observed ran normal first second
#print axioms certificate_15
/-- Instance 346:95965c546ae80dd61779, scalar event 30725. -/
def sourceState_16 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 1) (UScalar.size .Usize)) 2 effects
theorem certificate_16 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 1) (UScalar.size .Usize)) 2 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 1) (UScalar.size .Usize)) 2 effects observed ran normal first second
#print axioms certificate_16
/-- Instance 346:95965c546ae80dd61779, scalar event 30730. -/
def sourceState_17 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 2) (UScalar.size .Usize)) 1 effects
theorem certificate_17 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 2) (UScalar.size .Usize)) 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 2) (UScalar.size .Usize)) 1 effects observed ran normal first second
#print axioms certificate_17
/-- Instance 346:95965c546ae80dd61779, scalar event 30735. -/
def sourceState_18 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 3) (UScalar.size .Usize)) 0 effects
theorem certificate_18 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 3) (UScalar.size .Usize)) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 4) (.bounded input0 4) (UScalar.size .Usize)) (.literal 3) (UScalar.size .Usize)) 0 effects observed ran normal first second
#print axioms certificate_18
/-- Instance 432:95965c546ae80dd61779, scalar event 30908. -/
def sourceState_19 (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input0 3) 0 effects
theorem certificate_19 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.bitAnd input0 3) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.bitAnd input0 3) 0 effects observed ran normal first second
#print axioms certificate_19
end PV_B3P_ComputedIndices583227
