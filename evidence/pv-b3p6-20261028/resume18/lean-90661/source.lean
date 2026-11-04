import PV_B3P_RangeEvents578227
namespace PV_B3P_NestedIndices587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Checked nested frame: source event 245:95965c546ae80dd61779:30546. -/
def sourceState_0 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 14 0 index effects
theorem certificate_0 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 14 0 index effects observed ran normal first second
#print axioms certificate_0
/-- Checked nested frame: source event 494:95965c546ae80dd61779:30948. -/
def sourceState_1 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 4 0 index effects
theorem certificate_1 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_1 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_1
/-- Checked nested frame: source event 320:95965c546ae80dd61779:30584. -/
def sourceState_2 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_2 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_2 handler start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_2
/-- Checked nested frame: source event 320:95965c546ae80dd61779:30589. -/
def sourceState_3 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_3 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_3 handler start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_3
/-- Checked nested frame: source event 320:95965c546ae80dd61779:30599. -/
def sourceState_4 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_4 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_4 handler start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_4
/-- Checked nested frame: source event 320:95965c546ae80dd61779:30609. -/
def sourceState_5 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_5 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_5 handler start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_5
/-- Checked nested frame: source event 320:95965c546ae80dd61779:30619. -/
def sourceState_6 (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeEvents578227.sourceEvent handler ⟨start,3#usize⟩ 0 effects
theorem certificate_6 {α : Type} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_6 handler start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨start,3#usize⟩ 0 effects observed ran normal first second
#print axioms certificate_6
end PV_B3P_NestedIndices587227
