import PV_B3P_DominatedEvents578227
namespace PV_B3P_DominatedIndices578227_00
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_DominatedEvents578227
set_option autoImplicit false
/-- Instance 1:95965c546ae80dd61779, instruction 29187, strict test 81. -/
def sourceState_0 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 84 0 index effects
theorem certificate_0 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 84 0 index effects observed ran normal first second
#print axioms certificate_0
/-- Instance 7:95965c546ae80dd61779, instruction 29198, strict test 792. -/
def sourceState_1 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_1 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_1 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_1
/-- Instance 7:95965c546ae80dd61779, instruction 29203, strict test 850. -/
def sourceState_2 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_2 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_2 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_2
/-- Instance 7:95965c546ae80dd61779, instruction 29208, strict test 908. -/
def sourceState_3 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_3 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_3 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_3
/-- Instance 56:95965c546ae80dd61779, instruction 29451, strict test 5199. -/
def sourceState_4 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 10 6 index effects
theorem certificate_4 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_4 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 10 6 index effects observed ran normal first second
#print axioms certificate_4
/-- Instance 56:95965c546ae80dd61779, instruction 29456, strict test 5199. -/
def sourceState_5 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 10 6 index effects
theorem certificate_5 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_5 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 10 6 index effects observed ran normal first second
#print axioms certificate_5
/-- Instance 56:95965c546ae80dd61779, instruction 29461, strict test 5199. -/
def sourceState_6 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 10 23 index effects
theorem certificate_6 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_6 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 10 23 index effects observed ran normal first second
#print axioms certificate_6
/-- Instance 56:95965c546ae80dd61779, instruction 29466, strict test 5305. -/
def sourceState_7 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 10 6 index effects
theorem certificate_7 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_7 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 10 6 index effects observed ran normal first second
#print axioms certificate_7
/-- Instance 56:95965c546ae80dd61779, instruction 29471, strict test 5305. -/
def sourceState_8 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 10 6 index effects
theorem certificate_8 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_8 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 10 6 index effects observed ran normal first second
#print axioms certificate_8
/-- Instance 56:95965c546ae80dd61779, instruction 29481, strict test 5414. -/
def sourceState_9 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 10 6 index effects
theorem certificate_9 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_9 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 10 6 index effects observed ran normal first second
#print axioms certificate_9
/-- Instance 56:95965c546ae80dd61779, instruction 29486, strict test 5414. -/
def sourceState_10 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 10 6 index effects
theorem certificate_10 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_10 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 10 6 index effects observed ran normal first second
#print axioms certificate_10
/-- Instance 58:95965c546ae80dd61779, instruction 29572, strict test 6973. -/
def sourceState_11 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 20 0 index effects
theorem certificate_11 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_11 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 20 0 index effects observed ran normal first second
#print axioms certificate_11
/-- Instance 59:b4548570fddcc1efb85f, instruction 29584, strict test 7173. -/
def sourceState_12 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_12 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_12 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_12
/-- Instance 59:3ee816ee3badc75d5ede, instruction 29584, strict test 7173. -/
def sourceState_13 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_13 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_13 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_13
/-- Instance 231:95965c546ae80dd61779, instruction 30190, strict test 16185. -/
def sourceState_14 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_14 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_14 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_14
/-- Instance 231:95965c546ae80dd61779, instruction 30195, strict test 16185. -/
def sourceState_15 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_15 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_15 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_15
/-- Instance 231:95965c546ae80dd61779, instruction 30200, strict test 16185. -/
def sourceState_16 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 16 0 index effects
theorem certificate_16 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_16 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 16 0 index effects observed ran normal first second
#print axioms certificate_16
/-- Instance 59:412c274a9954e734bc86, instruction 29584, strict test 7173. -/
def sourceState_17 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_17 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_17 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_17
/-- Instance 59:5a23c8cad0af20d0f4fb, instruction 29584, strict test 7173. -/
def sourceState_18 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_18 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_18 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_18
/-- Instance 59:d86379aa4e1f98af6102, instruction 29584, strict test 7173. -/
def sourceState_19 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_19 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_19 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_19
/-- Instance 59:b58ea6f00dc81e4bbc15, instruction 29584, strict test 7173. -/
def sourceState_20 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_20 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_20 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_20
/-- Instance 248:95965c546ae80dd61779, instruction 30556, strict test 21322. -/
def sourceState_21 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 64 0 index effects
theorem certificate_21 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_21 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 64 0 index effects observed ran normal first second
#print axioms certificate_21
/-- Instance 248:95965c546ae80dd61779, instruction 30551, strict test 21322. -/
def sourceState_22 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 64 0 index effects
theorem certificate_22 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_22 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 64 0 index effects observed ran normal first second
#print axioms certificate_22
/-- Instance 346:95965c546ae80dd61779, instruction 30740, strict test 23727. -/
def sourceState_23 (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent 4 0 index effects
theorem certificate_23 {α : Type} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_23 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate 4 0 index effects observed ran normal first second
#print axioms certificate_23
end PV_B3P_DominatedIndices578227_00
