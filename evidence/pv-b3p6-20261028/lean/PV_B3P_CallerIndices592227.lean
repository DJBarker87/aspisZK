import PV_B3P_RangeComputedEvents592227
namespace PV_B3P_CallerIndices592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Actual incoming 7:815 -> 15:95965c546ae80dd61779:29259. -/
theorem certificate_15_0 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.bounded input0 16) (UScalar.size .Usize)) 68 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.bounded input0 16) (UScalar.size .Usize)) 68 effects observed ran normal first second
#print axioms certificate_15_0
/-- Actual incoming 7:873 -> 15:95965c546ae80dd61779:29259. -/
theorem certificate_15_1 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 1) (.literal 28) (UScalar.size .Usize)) (.bounded input0 16) (UScalar.size .Usize)) 40 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 1) (.literal 28) (UScalar.size .Usize)) (.bounded input0 16) (UScalar.size .Usize)) 40 effects observed ran normal first second
#print axioms certificate_15_1
/-- Actual incoming 7:931 -> 15:95965c546ae80dd61779:29259. -/
theorem certificate_15_2 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 2) (.literal 28) (UScalar.size .Usize)) (.bounded input0 16) (UScalar.size .Usize)) 12 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 2) (.literal 28) (UScalar.size .Usize)) (.bounded input0 16) (UScalar.size .Usize)) 12 effects observed ran normal first second
#print axioms certificate_15_2
/-- Actual incoming 7:996 -> 15:95965c546ae80dd61779:29259. -/
theorem certificate_15_3 {α : Type} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.add (.literal 16) (.bounded input0 10) (UScalar.size .Usize)) (UScalar.size .Usize)) 58 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.add (.literal 16) (.bounded input0 10) (UScalar.size .Usize)) (UScalar.size .Usize)) 58 effects observed ran normal first second
#print axioms certificate_15_3
/-- Actual incoming 7:1150 -> 15:95965c546ae80dd61779:29259. -/
theorem certificate_15_4 {α : Type}  (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.literal 26) (UScalar.size .Usize)) 57 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.literal 26) (UScalar.size .Usize)) 57 effects observed ran normal first second
#print axioms certificate_15_4
/-- Actual incoming 7:1459 -> 15:95965c546ae80dd61779:29259. -/
theorem certificate_15_5 {α : Type}  (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_ArithmeticEvents583227.sourceEvent (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.literal 27) (UScalar.size .Usize)) 56 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate (.add (.mul (.literal 0) (.literal 28) (UScalar.size .Usize)) (.literal 27) (UScalar.size .Usize)) 56 effects observed ran normal first second
#print axioms certificate_15_5
/-- Actual incoming 14:2149 -> 39:95965c546ae80dd61779:29305. -/
theorem certificate_39_0 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,20#usize⟩ (fun item => (.bounded item.val 20)) 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,20#usize⟩ (fun item => (.bounded item.val 20)) 1 effects observed ran normal first second
#print axioms certificate_39_0
/-- Actual incoming 14:2176 -> 39:95965c546ae80dd61779:29305. -/
theorem certificate_39_1 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,20#usize⟩ (fun item => (.bounded item.val 20)) 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,20#usize⟩ (fun item => (.bounded item.val 20)) 1 effects observed ran normal first second
#print axioms certificate_39_1
/-- Actual incoming 58:6800 -> 39:95965c546ae80dd61779:29305. -/
theorem certificate_39_2 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,20#usize⟩ (fun item => (.bounded item.val 20)) 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,20#usize⟩ (fun item => (.bounded item.val 20)) 1 effects observed ran normal first second
#print axioms certificate_39_2
/-- Actual incoming 58:6512 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_0 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_240_0
/-- Actual incoming 58:6563 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_1 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_240_1
/-- Actual incoming 58:6619 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_2 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_240_2
/-- Actual incoming 58:6676 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_3 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_240_3
/-- Actual incoming 58:6813 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_4 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 8) (.bounded item.val 8) (UScalar.size .Usize))) 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 8) (.bounded item.val 8) (UScalar.size .Usize))) 0 effects observed ran normal first second
#print axioms certificate_240_4
/-- Actual incoming 58:6875 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_5 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_240_5
/-- Actual incoming 58:6946 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_6 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_240_6
/-- Actual incoming 58:7027 -> 240:95965c546ae80dd61779:30468. -/
theorem certificate_240_7 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 0) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_240_7
theorem mask_column {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_DominatedEvents578227.sourceEvent 10 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 10 0 index effects observed ran normal first second
#print axioms mask_column
end PV_B3P_CallerIndices592227
