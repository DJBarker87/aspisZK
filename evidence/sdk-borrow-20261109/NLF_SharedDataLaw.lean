import NLF_WrapperFlagLaws
set_option autoImplicit false
namespace NLF_SharedDataLaw
open NLF_RefCell NLF_SdkModel NLF_WrapperFlagLaws
/-- Complete wrapper Result, on its SAME projected cell. Ghost freshness is
established by the parent invariant, not a restriction on native accounts. -/
theorem result (s : State) (a t : Nat)
    (fresh : t∉(s.cells (s.accounts a).data).readers) :
    try_borrow_data s a t =
      if sharedAllowed s (s.accounts a).data then
        (put s (s.accounts a).data {s.cells (s.accounts a).data with readers:=t::(s.cells (s.accounts a).data).readers},
         .ok ⟨(s.accounts a).data,t,.shared⟩)
      else (s,.error .accountBorrowFailed) := shared_complete s _ t fresh
#print axioms result
end NLF_SharedDataLaw
