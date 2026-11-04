import PV_B3P_TableEvents592227
import PV_B3P_InclusiveEvents592227
import PV_B3P_RangeEvents578227
namespace PV_B3P_FoldIndices592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
def value1 : Fin 16 := ⟨1,by decide⟩
def value9 : Fin 16 := ⟨9,by decide⟩
def value10 : Fin 16 := ⟨10,by decide⟩
def sourceValues : List (List (Fin 16)) := [[value1,value9,value10]]
/-- Actual VALUE-domain source event at 195:29757. -/
theorem array_value {α : Type} (cursor : Nat) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_TableEvents592227.sourceEvent 16 sourceValues 0 cursor effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_TableEvents592227.event_certificate 16 sourceValues 0 cursor effects observed ran normal first second
#print axioms array_value
/-- Actual VALUE-domain source event at 197:29762. -/
theorem inclusive_value {α : Type} (handler : Str → Result Never) (current : Usize) (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,8#usize,exhausted⟩ 7 effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,8#usize,exhausted⟩ 7 effects observed ran normal first second
#print axioms inclusive_value
/-- Actual VALUE-domain source event at 43:29350. -/
theorem range_0_0 {α : Type} (handler : Str → Result Never) (current : Usize) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨current,57#usize⟩ 7 effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨current,57#usize⟩ 7 effects observed ran normal first second
#print axioms range_0_0
/-- Actual VALUE-domain source event at 43:29350. -/
theorem range_1_0 {α : Type} (handler : Str → Result Never) (current : Usize) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨current,63#usize⟩ 1 effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨current,63#usize⟩ 1 effects observed ran normal first second
#print axioms range_1_0
/-- Actual VALUE-domain source event at 43:29350. -/
theorem range_2_0 {α : Type} (handler : Str → Result Never) (current : Usize) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨current,25#usize⟩ 39 effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨current,25#usize⟩ 39 effects observed ran normal first second
#print axioms range_2_0
/-- Actual VALUE-domain source event at 43:29350. -/
theorem range_2_1 {α : Type} (handler : Str → Result Never) (current : Usize) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_RangeEvents578227.sourceEvent handler ⟨current,57#usize⟩ 7 effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeEvents578227.event_certificate handler ⟨current,57#usize⟩ 7 effects observed ran normal first second
#print axioms range_2_1
end PV_B3P_FoldIndices592227
