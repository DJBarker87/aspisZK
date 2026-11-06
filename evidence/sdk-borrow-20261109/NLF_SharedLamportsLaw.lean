import NLF_WrapperFlagLaws
set_option autoImplicit false
namespace NLF_SharedLamportsLaw
open NLF_RefCell NLF_SdkModel NLF_WrapperFlagLaws
/-- Complete wrapper Result, on its SAME projected cell. Ghost freshness is
established by the parent invariant, not a restriction on native accounts. -/
theorem result (s : State) (a t : Nat)
    (fresh : t∉(s.cells (s.accounts a).lamports).readers) :
    try_borrow_lamports s a t =
      if sharedAllowed s (s.accounts a).lamports then
        (put s (s.accounts a).lamports {s.cells (s.accounts a).lamports with readers:=t::(s.cells (s.accounts a).lamports).readers},
         .ok ⟨(s.accounts a).lamports,t,.shared⟩)
      else (s,.error .accountBorrowFailed) := shared_complete s _ t fresh
#print axioms result
end NLF_SharedLamportsLaw
