import PCC_ZeroedReference
set_option autoImplicit false
namespace PCC
open PCA
/-- No data_len or try_borrow_data is entered on an owner mismatch. -/
theorem zeroed_wrong_owner (args : Nat × Key) (s : PCA_State)
    (h : (s.loans.state.accounts args.1).owner ≠ args.2.toList) :
    zeroedReference args s = ⟨s,[],.ok false⟩ := by
  simp [zeroedReference,Reference.pure,h]
#print axioms zeroed_wrong_owner
end PCC
