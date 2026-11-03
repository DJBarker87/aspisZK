import PV_B3P_WindowEvents578227
namespace PV_B3P_WindowIndices578227_00
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_WindowEvents578227
set_option autoImplicit false
/-- Actual source instance 59:b4548570fddcc1efb85f, instruction 29579. -/
def sourceState_0 (base value : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent base 8#usize value 0 effects
theorem certificate_0 {α : Type} (base value : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 base value effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate base 8#usize value 0 effects observed ran normal first second
#print axioms certificate_0
/-- Actual source instance 59:3ee816ee3badc75d5ede, instruction 29579. -/
def sourceState_1 (base value : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent base 2#usize value 0 effects
theorem certificate_1 {α : Type} (base value : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_1 base value effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate base 2#usize value 0 effects observed ran normal first second
#print axioms certificate_1
/-- Actual source instance 59:412c274a9954e734bc86, instruction 29579. -/
def sourceState_2 (base value : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent base 16#usize value 0 effects
theorem certificate_2 {α : Type} (base value : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_2 base value effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate base 16#usize value 0 effects observed ran normal first second
#print axioms certificate_2
/-- Actual source instance 59:5a23c8cad0af20d0f4fb, instruction 29579. -/
def sourceState_3 (base value : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent base 17#usize value 0 effects
theorem certificate_3 {α : Type} (base value : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_3 base value effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate base 17#usize value 0 effects observed ran normal first second
#print axioms certificate_3
/-- Actual source instance 59:d86379aa4e1f98af6102, instruction 29579. -/
def sourceState_4 (base value : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent base 33#usize value 0 effects
theorem certificate_4 {α : Type} (base value : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_4 base value effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate base 33#usize value 0 effects observed ran normal first second
#print axioms certificate_4
/-- Actual source instance 59:b58ea6f00dc81e4bbc15, instruction 29579. -/
def sourceState_5 (base value : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent base 12#usize value 0 effects
theorem certificate_5 {α : Type} (base value : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_5 base value effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate base 12#usize value 0 effects observed ran normal first second
#print axioms certificate_5
end PV_B3P_WindowIndices578227_00
