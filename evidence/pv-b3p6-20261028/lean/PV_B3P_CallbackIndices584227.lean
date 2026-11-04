import PV_B3P_DominatedEvents578227
namespace PV_B3P_CallbackIndices584227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_DominatedEvents578227
set_option autoImplicit false
/-- Caller initializer test, two checked tuple forwards, source event 199:95965c546ae80dd61779:29767. -/
def sourceState_0 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_0 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_0
/-- Caller initializer test, two checked tuple forwards, source event 199:95965c546ae80dd61779:29772. -/
def sourceState_1 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_1 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_1 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_1
/-- Caller initializer test, two checked tuple forwards, source event 428:95965c546ae80dd61779:30868. -/
def sourceState_2 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_2 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_2 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_2
/-- Caller initializer test, two checked tuple forwards, source event 428:95965c546ae80dd61779:30878. -/
def sourceState_3 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_3 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_3 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_3
/-- Caller initializer test, two checked tuple forwards, source event 428:95965c546ae80dd61779:30888. -/
def sourceState_4 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_4 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_4 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_4
/-- Caller initializer test, two checked tuple forwards, source event 428:95965c546ae80dd61779:30898. -/
def sourceState_5 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_5 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_5 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_5
/-- Caller initializer test, two checked tuple forwards, source event 432:95965c546ae80dd61779:30903. -/
def sourceState_6 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_6 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_6 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_6
/-- Caller initializer test, two checked tuple forwards, source event 432:95965c546ae80dd61779:30913. -/
def sourceState_7 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_7 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_7 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_7
/-- Caller initializer test, two checked tuple forwards, source event 504:95965c546ae80dd61779:31178. -/
def sourceState_8 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_8 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_8 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_8
/-- Caller initializer test, two checked tuple forwards, source event 504:95965c546ae80dd61779:31183. -/
def sourceState_9 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_9 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_9 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_9
/-- Caller initializer test, two checked tuple forwards, source event 506:95965c546ae80dd61779:31188. -/
def sourceState_10 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_10 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_10 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_10
/-- Caller initializer test, two checked tuple forwards, source event 506:95965c546ae80dd61779:31193. -/
def sourceState_11 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_11 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_11 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_11
/-- Caller initializer test, two checked tuple forwards, source event 508:95965c546ae80dd61779:31198. -/
def sourceState_12 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_12 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_12 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_12
/-- Caller initializer test, two checked tuple forwards, source event 508:95965c546ae80dd61779:31203. -/
def sourceState_13 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_13 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_13 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_13
/-- Caller initializer test, two checked tuple forwards, source event 524:95965c546ae80dd61779:31243. -/
def sourceState_14 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_14 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_14 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_14
/-- Caller initializer test, two checked tuple forwards, source event 524:95965c546ae80dd61779:31253. -/
def sourceState_15 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_15 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_15 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_15
/-- Caller initializer test, two checked tuple forwards, source event 524:95965c546ae80dd61779:31263. -/
def sourceState_16 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_16 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_16 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_16
/-- Caller initializer test, two checked tuple forwards, source event 524:95965c546ae80dd61779:31273. -/
def sourceState_17 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_17 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_17 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_17
/-- Caller initializer test, two checked tuple forwards, source event 536:95965c546ae80dd61779:31283. -/
def sourceState_18 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_18 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_18 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_18
/-- Caller initializer test, two checked tuple forwards, source event 536:95965c546ae80dd61779:31293. -/
def sourceState_19 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_19 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_19 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_19
/-- Caller initializer test, two checked tuple forwards, source event 536:95965c546ae80dd61779:31303. -/
def sourceState_20 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_20 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_20 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_20
/-- Caller initializer test, two checked tuple forwards, source event 536:95965c546ae80dd61779:31313. -/
def sourceState_21 (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 count effects
theorem certificate_21 {α : Type} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_21 count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 count effects observed ran normal first second
#print axioms certificate_21
end PV_B3P_CallbackIndices584227
