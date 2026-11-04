import PV_B3P_RangeEvents578227
import PV_B3P_DominatedEvents578227
import PV_B3P_FixedIndex572227
namespace PV_B3P_NormalizedIndices583227_01
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29968. -/
def sourceState_24 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_24 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_24
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29973. -/
def sourceState_25 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_25 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_25
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29978. -/
def sourceState_26 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_26 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_26
/-- Local scalar projection: instance 221:95965c546ae80dd61779, statement 29983. -/
def sourceState_27 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_27 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_27
/-- Local scalar projection: instance 222:95965c546ae80dd61779, statement 29988. -/
def sourceState_28 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_28 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_28
/-- Local scalar projection: instance 222:95965c546ae80dd61779, statement 29993. -/
def sourceState_29 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_29 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_29
/-- Local scalar projection: instance 222:95965c546ae80dd61779, statement 29998. -/
def sourceState_30 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_30 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_30
/-- Local scalar projection: instance 223:95965c546ae80dd61779, statement 30003. -/
def sourceState_31 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_31 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_31
/-- Local scalar projection: instance 223:95965c546ae80dd61779, statement 30008. -/
def sourceState_32 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_32 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_32
/-- Local scalar projection: instance 223:95965c546ae80dd61779, statement 30013. -/
def sourceState_33 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_33 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_33
/-- Local scalar projection: instance 231:95965c546ae80dd61779, statement 30280. -/
def sourceState_34 : IndexState := ⟨8,16⟩
theorem certificate_34 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_34) ∧
      branch (indexGuard sourceState_34) normal first = branch (indexGuard sourceState_34) normal second :=
  PV_B3P_FixedIndex572227.fixed_certificate 8 7 normal first second
#print axioms certificate_34
/-- Local scalar projection: instance 231:95965c546ae80dd61779, statement 30290. -/
def sourceState_35 : IndexState := ⟨8,16⟩
theorem certificate_35 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_35) ∧
      branch (indexGuard sourceState_35) normal first = branch (indexGuard sourceState_35) normal second :=
  PV_B3P_FixedIndex572227.fixed_certificate 8 7 normal first second
#print axioms certificate_35
/-- Local scalar projection: instance 232:95965c546ae80dd61779, statement 30366. -/
def sourceState_36 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects
theorem certificate_36 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 8 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,8#usize⟩ 8 effects observed ran normal first second
#print axioms certificate_36
/-- Local scalar projection: instance 240:95965c546ae80dd61779, statement 30458. -/
def sourceState_37 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 0 effects
theorem certificate_37 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,8#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_37
/-- Local scalar projection: instance 240:95965c546ae80dd61779, statement 30463. -/
def sourceState_38 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 0 effects
theorem certificate_38 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,8#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_38
/-- Local scalar projection: instance 240:95965c546ae80dd61779, statement 30473. -/
def sourceState_39 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 0 effects
theorem certificate_39 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,8#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,8#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_39
/-- Local scalar projection: instance 245:95965c546ae80dd61779, statement 30511. -/
def sourceState_40 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_40 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_40
/-- Local scalar projection: instance 245:95965c546ae80dd61779, statement 30541. -/
def sourceState_41 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 14 0 index effects
theorem certificate_41 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 14 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 14 0 index effects observed ran normal first second
#print axioms certificate_41
/-- Local scalar projection: instance 245:95965c546ae80dd61779, statement 30536. -/
def sourceState_42 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_42 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_42
/-- Local scalar projection: instance 245:95965c546ae80dd61779, statement 30516. -/
def sourceState_43 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_43 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_43
/-- Local scalar projection: instance 245:95965c546ae80dd61779, statement 30526. -/
def sourceState_44 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_44 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_44
/-- Local scalar projection: instance 245:95965c546ae80dd61779, statement 30531. -/
def sourceState_45 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_45 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_45
/-- Local scalar projection: instance 362:95965c546ae80dd61779, statement 30796. -/
def sourceState_46 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects
theorem certificate_46 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_DominatedEvents578227.sourceEvent 16 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_46
/-- Local scalar projection: instance 362:95965c546ae80dd61779, statement 30801. -/
def sourceState_47 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects
theorem certificate_47 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,16#usize⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,16#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_47
end PV_B3P_NormalizedIndices583227_01
