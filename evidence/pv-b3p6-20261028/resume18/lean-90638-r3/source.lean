import PV_B3P_RangeEvents578227
import PV_B3P_DominatedEvents578227
import PV_B3P_FixedIndex572227
namespace PV_B3P_NormalizedIndices583227_00
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Local scalar projection: instance 21:95965c546ae80dd61779, statement 29285. -/
def sourceState_0 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 136 0 index effects
theorem certificate_0 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 136 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 136 0 index effects observed ran normal first second
#print axioms certificate_0
/-- Local scalar projection: instance 48:95965c546ae80dd61779, statement 29355. -/
def sourceState_1 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects
theorem certificate_1 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,8#usize⟩ 8 effects observed ran normal first second
#print axioms certificate_1
/-- Local scalar projection: instance 48:95965c546ae80dd61779, statement 29360. -/
def sourceState_2 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects
theorem certificate_2 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,8#usize⟩ 8 effects observed ran normal first second
#print axioms certificate_2
/-- Local scalar projection: instance 48:95965c546ae80dd61779, statement 29365. -/
def sourceState_3 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects
theorem certificate_3 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,8#usize⟩ 8 effects observed ran normal first second
#print axioms certificate_3
/-- Local scalar projection: instance 218:95965c546ae80dd61779, statement 29802. -/
def sourceState_4 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_4 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_4
/-- Local scalar projection: instance 219:95965c546ae80dd61779, statement 29812. -/
def sourceState_5 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_5 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_5
/-- Local scalar projection: instance 219:95965c546ae80dd61779, statement 29817. -/
def sourceState_6 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_6 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_6
/-- Local scalar projection: instance 219:95965c546ae80dd61779, statement 29822. -/
def sourceState_7 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_7 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_7
/-- Local scalar projection: instance 219:95965c546ae80dd61779, statement 29827. -/
def sourceState_8 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_8 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_8
/-- Local scalar projection: instance 219:95965c546ae80dd61779, statement 29832. -/
def sourceState_9 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_9 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_9
/-- Local scalar projection: instance 220:95965c546ae80dd61779, statement 29837. -/
def sourceState_10 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_10 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_10
/-- Local scalar projection: instance 220:95965c546ae80dd61779, statement 29842. -/
def sourceState_11 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_11 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_11
/-- Local scalar projection: instance 220:95965c546ae80dd61779, statement 29847. -/
def sourceState_12 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_12 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_12
/-- Local scalar projection: instance 220:95965c546ae80dd61779, statement 29852. -/
def sourceState_13 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_13 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_13
/-- Local scalar projection: instance 220:95965c546ae80dd61779, statement 29857. -/
def sourceState_14 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_14 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_14
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29878. -/
def sourceState_15 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_15 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_15
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29883. -/
def sourceState_16 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_16 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_16
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29888. -/
def sourceState_17 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_17 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_17
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29908. -/
def sourceState_18 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_18 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_18
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29913. -/
def sourceState_19 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_19 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_19
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29918. -/
def sourceState_20 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_20 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_20
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29938. -/
def sourceState_21 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_21 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_21
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29943. -/
def sourceState_22 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_22 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_22
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29948. -/
def sourceState_23 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_23 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_23
end PV_B3P_NormalizedIndices583227_00
