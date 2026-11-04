import PV_B3P_RangeComputedEvents592227
namespace PV_B3P_RangeArithmetic592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Actual source Range next 17846 then scalar event 232:95965c546ae80dd61779:30361. -/
def sourceState_0 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 1) (.bounded item.val 8) (UScalar.size .Usize))) 7 effects
theorem certificate_0 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_0 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 1) (.bounded item.val 8) (UScalar.size .Usize))) 7 effects observed ran normal first second
#print axioms certificate_0
/-- Actual source Range next 17846 then scalar event 232:95965c546ae80dd61779:30371. -/
def sourceState_1 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 1) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects
theorem certificate_1 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_1 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 1) (.bounded item.val 8) (UScalar.size .Usize))) 8 effects observed ran normal first second
#print axioms certificate_1
/-- Actual source Range next 17846 then scalar event 232:95965c546ae80dd61779:30376. -/
def sourceState_2 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 8) (.bounded item.val 8) (UScalar.size .Usize))) 0 effects
theorem certificate_2 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_2 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 8) (.bounded item.val 8) (UScalar.size .Usize))) 0 effects observed ran normal first second
#print axioms certificate_2
/-- Actual source Range next 17846 then scalar event 232:95965c546ae80dd61779:30381. -/
def sourceState_3 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.add (.literal 1) (.literal 8) (UScalar.size .Usize)) (.bounded item.val 8) (UScalar.size .Usize))) 0 effects
theorem certificate_3 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_3 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.add (.literal 1) (.literal 8) (UScalar.size .Usize)) (.bounded item.val 8) (UScalar.size .Usize))) 0 effects observed ran normal first second
#print axioms certificate_3
/-- Actual source Range next 18711 then scalar event 239:95965c546ae80dd61779:30408. -/
def sourceState_4 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 2) (.bounded item.val 8) (UScalar.size .Usize))) 6 effects
theorem certificate_4 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_4 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 2) (.bounded item.val 8) (UScalar.size .Usize))) 6 effects observed ran normal first second
#print axioms certificate_4
/-- Actual source Range next 18711 then scalar event 239:95965c546ae80dd61779:30413. -/
def sourceState_5 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨start,8#usize⟩ (fun item => (.add (.literal 3) (.bounded item.val 8) (UScalar.size .Usize))) 1 effects
theorem certificate_5 {α : Type} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_5 handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate handler ⟨start,8#usize⟩ (fun item => (.add (.literal 3) (.bounded item.val 8) (UScalar.size .Usize))) 1 effects observed ran normal first second
#print axioms certificate_5
end PV_B3P_RangeArithmetic592227
