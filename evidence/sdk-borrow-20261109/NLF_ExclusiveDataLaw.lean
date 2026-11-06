import NLF_WrapperFlagLaws
set_option autoImplicit false
namespace NLF_ExclusiveDataLaw
open NLF_RefCell NLF_SdkModel NLF_WrapperFlagLaws
/-- Complete wrapper Result, on its SAME projected cell. Ghost freshness is
established by the parent invariant, not a restriction on native accounts. -/
theorem result (s : State) (a t : Nat) :
    try_borrow_mut_data s a t =
      if flag (s.cells (s.accounts a).data)=0 then
        (put s (s.accounts a).data {s.cells (s.accounts a).data with writer:=some t},
         .ok ⟨(s.accounts a).data,t,.exclusive⟩)
      else (s,.error .accountBorrowFailed) := exclusive_complete s _ t
#print axioms result
end NLF_ExclusiveDataLaw
