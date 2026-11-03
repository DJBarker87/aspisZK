import PV_B3P_FixedIndex572227
import PV_B3P_DominatedEvents578227
namespace PV_B3P_SpecializedIndices578227_00
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Exact const specialization 189:576636c9f73fe7ac811e, source instruction 29752. -/
def sourceState_0 : IndexState := ⟨0,64⟩
theorem certificate_0 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_0) ∧
      branch (indexGuard sourceState_0) normal first = branch (indexGuard sourceState_0) normal second :=
  PV_B3P_FixedIndex572227.fixed_certificate 0 63 normal first second
#print axioms certificate_0
/-- Exact const specialization 189:412c274a9954e734bc86, source instruction 29752. -/
def sourceState_1 : IndexState := ⟨0,16⟩
theorem certificate_1 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_1) ∧
      branch (indexGuard sourceState_1) normal first = branch (indexGuard sourceState_1) normal second :=
  PV_B3P_FixedIndex572227.fixed_certificate 0 15 normal first second
#print axioms certificate_1
end PV_B3P_SpecializedIndices578227_00
