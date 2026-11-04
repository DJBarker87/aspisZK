import PV_B3P_InclusiveEvents592227
namespace PV_B3P_PreweightedIndices592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Actual 19:2870, start=92, N=2, last=23. -/
theorem certificate_3ee816ee3badc75d5ede_29589_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,23#usize,exhausted⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,23#usize,exhausted⟩ 0 effects observed ran normal first second
#print axioms certificate_3ee816ee3badc75d5ede_29589_0
/-- Actual 56:6339, start=82, N=2, last=20. -/
theorem certificate_3ee816ee3badc75d5ede_29589_1 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,20#usize,exhausted⟩ 3 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,20#usize,exhausted⟩ 3 effects observed ran normal first second
#print axioms certificate_3ee816ee3badc75d5ede_29589_1
/-- Actual 19:2870, start=92, N=2, last=23. -/
theorem certificate_3ee816ee3badc75d5ede_29594_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,23#usize,exhausted⟩ 0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,23#usize,exhausted⟩ 0 effects observed ran normal first second
#print axioms certificate_3ee816ee3badc75d5ede_29594_0
/-- Actual 56:6339, start=82, N=2, last=20. -/
theorem certificate_3ee816ee3badc75d5ede_29594_1 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,20#usize,exhausted⟩ 3 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,20#usize,exhausted⟩ 3 effects observed ran normal first second
#print axioms certificate_3ee816ee3badc75d5ede_29594_1
/-- Actual 54:4724, start=0, N=16, last=3. -/
theorem certificate_412c274a9954e734bc86_29589_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,3#usize,exhausted⟩ 20 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,3#usize,exhausted⟩ 20 effects observed ran normal first second
#print axioms certificate_412c274a9954e734bc86_29589_0
/-- Actual 54:4741, start=16, N=16, last=7. -/
theorem certificate_412c274a9954e734bc86_29589_1 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,7#usize,exhausted⟩ 16 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,7#usize,exhausted⟩ 16 effects observed ran normal first second
#print axioms certificate_412c274a9954e734bc86_29589_1
/-- Actual 54:4724, start=0, N=16, last=3. -/
theorem certificate_412c274a9954e734bc86_29594_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,3#usize,exhausted⟩ 20 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,3#usize,exhausted⟩ 20 effects observed ran normal first second
#print axioms certificate_412c274a9954e734bc86_29594_0
/-- Actual 54:4741, start=16, N=16, last=7. -/
theorem certificate_412c274a9954e734bc86_29594_1 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,7#usize,exhausted⟩ 16 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,7#usize,exhausted⟩ 16 effects observed ran normal first second
#print axioms certificate_412c274a9954e734bc86_29594_1
/-- Actual 55:4906, start=32, N=17, last=12. -/
theorem certificate_5a23c8cad0af20d0f4fb_29589_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,12#usize,exhausted⟩ 11 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,12#usize,exhausted⟩ 11 effects observed ran normal first second
#print axioms certificate_5a23c8cad0af20d0f4fb_29589_0
/-- Actual 55:4906, start=32, N=17, last=12. -/
theorem certificate_5a23c8cad0af20d0f4fb_29594_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,12#usize,exhausted⟩ 11 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,12#usize,exhausted⟩ 11 effects observed ran normal first second
#print axioms certificate_5a23c8cad0af20d0f4fb_29594_0
/-- Actual 19:2629, start=84, N=8, last=22. -/
theorem certificate_b4548570fddcc1efb85f_29589_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,22#usize,exhausted⟩ 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,22#usize,exhausted⟩ 1 effects observed ran normal first second
#print axioms certificate_b4548570fddcc1efb85f_29589_0
/-- Actual 19:2629, start=84, N=8, last=22. -/
theorem certificate_b4548570fddcc1efb85f_29594_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,22#usize,exhausted⟩ 1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,22#usize,exhausted⟩ 1 effects observed ran normal first second
#print axioms certificate_b4548570fddcc1efb85f_29594_0
/-- Actual 57:6447, start=0, N=12, last=2. -/
theorem certificate_b58ea6f00dc81e4bbc15_29589_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,2#usize,exhausted⟩ 21 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,2#usize,exhausted⟩ 21 effects observed ran normal first second
#print axioms certificate_b58ea6f00dc81e4bbc15_29589_0
/-- Actual 57:6447, start=0, N=12, last=2. -/
theorem certificate_b58ea6f00dc81e4bbc15_29594_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,2#usize,exhausted⟩ 21 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,2#usize,exhausted⟩ 21 effects observed ran normal first second
#print axioms certificate_b58ea6f00dc81e4bbc15_29594_0
/-- Actual 56:6048, start=49, N=33, last=20. -/
theorem certificate_d86379aa4e1f98af6102_29589_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,20#usize,exhausted⟩ 3 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,20#usize,exhausted⟩ 3 effects observed ran normal first second
#print axioms certificate_d86379aa4e1f98af6102_29589_0
/-- Actual 56:6048, start=49, N=33, last=20. -/
theorem certificate_d86379aa4e1f98af6102_29594_0 {α : Type} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent handler ⟨current,20#usize,exhausted⟩ 3 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate handler ⟨current,20#usize,exhausted⟩ 3 effects observed ran normal first second
#print axioms certificate_d86379aa4e1f98af6102_29594_0
end PV_B3P_PreweightedIndices592227
