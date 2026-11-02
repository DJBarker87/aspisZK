import PV_B3P_FixedIndex572227
namespace PV_B3P_FixedIndices572227_06
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227
set_option autoImplicit false
/-- Actual source instance 536:95965c546ae80dd61779, statement 31298. -/
def sourceState_192 : IndexState := ⟨2, 4⟩
theorem guard_192 : indexGuard sourceState_192 := fixed_guard 2 1
theorem certificate_192 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_192) ∧
      branch (indexGuard sourceState_192) normal first =
        branch (indexGuard sourceState_192) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_192
#print axioms certificate_192
/-- Actual source instance 536:95965c546ae80dd61779, statement 31308. -/
def sourceState_193 : IndexState := ⟨3, 4⟩
theorem guard_193 : indexGuard sourceState_193 := fixed_guard 3 0
theorem certificate_193 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_193) ∧
      branch (indexGuard sourceState_193) normal first =
        branch (indexGuard sourceState_193) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_193
#print axioms certificate_193
end PV_B3P_FixedIndices572227_06
