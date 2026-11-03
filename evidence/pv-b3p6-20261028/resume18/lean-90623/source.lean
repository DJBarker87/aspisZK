import PV_B3P_RangeEvents578227
namespace PV_B3P_RangeIndices578227_00
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_RangeEvents578227
set_option autoImplicit false
/-- Instance 58:95965c546ae80dd61779, instruction 29567, next call 6721. -/
def sourceState_0 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,20#usize⟩ 0 effects
theorem certificate_0 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_0 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,20#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_0
/-- Instance 224:95965c546ae80dd61779, instruction 30021, next call 13983. -/
def sourceState_1 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,4#usize⟩ 0 effects
theorem certificate_1 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_1 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,4#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_1
/-- Instance 224:95965c546ae80dd61779, instruction 30026, next call 13983. -/
def sourceState_2 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,4#usize⟩ 0 effects
theorem certificate_2 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_2 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,4#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_2
/-- Instance 224:95965c546ae80dd61779, instruction 30031, next call 13983. -/
def sourceState_3 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,4#usize⟩ 0 effects
theorem certificate_3 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_3 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,4#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_3
/-- Instance 320:95965c546ae80dd61779, instruction 30629, next call 22583. -/
def sourceState_4 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_4 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_4 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_4
/-- Instance 320:95965c546ae80dd61779, instruction 30634, next call 22583. -/
def sourceState_5 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_5 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_5 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_5
/-- Instance 320:95965c546ae80dd61779, instruction 30639, next call 22583. -/
def sourceState_6 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_6 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_6 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_6
/-- Instance 320:95965c546ae80dd61779, instruction 30644, next call 22583. -/
def sourceState_7 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_7 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_7 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_7
/-- Instance 320:95965c546ae80dd61779, instruction 30649, next call 22583. -/
def sourceState_8 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_8 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_8 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_8
/-- Instance 320:95965c546ae80dd61779, instruction 30654, next call 22583. -/
def sourceState_9 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_9 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_9 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_9
/-- Instance 320:95965c546ae80dd61779, instruction 30659, next call 22583. -/
def sourceState_10 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_10 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_10 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_10
/-- Instance 320:95965c546ae80dd61779, instruction 30664, next call 22583. -/
def sourceState_11 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_11 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_11 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_11
/-- Instance 320:95965c546ae80dd61779, instruction 30669, next call 22583. -/
def sourceState_12 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_12 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_12 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_12
/-- Instance 320:95965c546ae80dd61779, instruction 30674, next call 22583. -/
def sourceState_13 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_13 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_13 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_13
/-- Instance 320:95965c546ae80dd61779, instruction 30594, next call 22979. -/
def sourceState_14 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_14 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_14 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_14
/-- Instance 320:95965c546ae80dd61779, instruction 30604, next call 22979. -/
def sourceState_15 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_15 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_15 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_15
/-- Instance 320:95965c546ae80dd61779, instruction 30614, next call 22979. -/
def sourceState_16 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_16 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_16 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_16
/-- Instance 320:95965c546ae80dd61779, instruction 30624, next call 22979. -/
def sourceState_17 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_17 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_17 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_17
end PV_B3P_RangeIndices578227_00
