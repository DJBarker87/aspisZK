import PV_B3P_FixedIndex572227
namespace PV_B3P_FrameIndices578227_01
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227
set_option autoImplicit false
/-- Actual source instance 494:95965c546ae80dd61779, instruction 31143. -/
def sourceState_24 : IndexState := ⟨3, 4⟩
theorem certificate_24 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_24) ∧
      branch (indexGuard sourceState_24) normal first =
        branch (indexGuard sourceState_24) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms certificate_24
/-- Actual source instance 494:95965c546ae80dd61779, instruction 31153. -/
def sourceState_25 : IndexState := ⟨2, 4⟩
theorem certificate_25 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_25) ∧
      branch (indexGuard sourceState_25) normal first =
        branch (indexGuard sourceState_25) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms certificate_25
/-- Actual source instance 494:95965c546ae80dd61779, instruction 31163. -/
def sourceState_26 : IndexState := ⟨1, 4⟩
theorem certificate_26 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_26) ∧
      branch (indexGuard sourceState_26) normal first =
        branch (indexGuard sourceState_26) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms certificate_26
/-- Actual source instance 494:95965c546ae80dd61779, instruction 31173. -/
def sourceState_27 : IndexState := ⟨0, 4⟩
theorem certificate_27 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_27) ∧
      branch (indexGuard sourceState_27) normal first =
        branch (indexGuard sourceState_27) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms certificate_27
end PV_B3P_FrameIndices578227_01
