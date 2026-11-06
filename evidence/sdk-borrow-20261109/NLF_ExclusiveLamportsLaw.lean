import NLF_WrapperFlagLaws
set_option autoImplicit false
namespace NLF_ExclusiveLamportsLaw
open NLF_RefCell NLF_SdkModel NLF_WrapperFlagLaws
/-- Complete wrapper Result, on its SAME projected cell. Ghost freshness is
established by the parent invariant, not a restriction on native accounts. -/
theorem result (s : State) (a t : Nat) :
    try_borrow_mut_lamports s a t =
      if flag (s.cells (s.accounts a).lamports)=0 then
        (put s (s.accounts a).lamports {s.cells (s.accounts a).lamports with writer:=some t},
         .ok ⟨(s.accounts a).lamports,t,.exclusive⟩)
      else (s,.error .accountBorrowFailed) := exclusive_complete s _ t
#print axioms result
end NLF_ExclusiveLamportsLaw
