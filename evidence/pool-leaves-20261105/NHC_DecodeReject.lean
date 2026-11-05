import NHC_DecodeModel
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NHC_DecodeReject
/-- Exact wrong-size rejection for every input length, with no upper bound and
without an accepted-child or fixed-account-count premise. -/
theorem wrong_length (input : Slice U8) (count : Nat) (wrong : input.val.length ≠ 324) :
    NHC_DecodeModel.run input count = ok (.Err .InvalidInstructionData) := by
  by_cases small : input.val.length < 4
  · exact NHC_DecodeModel.short input count small
  · obtain ⟨body,hints,strip,window,_⟩ := NHC_HintsTotal.split input (by omega)
    have length : body.val.length = input.val.length-4 := by
      rw [window,List.length_take,Nat.min_eq_left (by omega)]
    have bad : body.val.length ≠ 320 := by omega
    have decode := NFY_NFD_RequestDomains.wrong_length body bad
    change AspisR1.NFY_JHd_RequestNative.decode body = _ at decode
    simp only [NHC_DecodeModel.run,strip,bind_tc_ok,decode,NHC_DecodeModel.afterDecode]
#print axioms wrong_length
end NHC_DecodeReject
