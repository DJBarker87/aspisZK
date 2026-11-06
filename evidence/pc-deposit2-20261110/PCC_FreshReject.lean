import PCC_FreshReference
set_option autoImplicit false
namespace PCC
open PCA
/-- Header rejection precedes every loan and every owner/data branch. -/
theorem fresh_header_reject (args : FreshArgs) (s : PCA_State)
    (h : let a := s.loans.state.accounts args.account
      a.key ≠ args.expected.toList ∨ a.executable = true ∨ a.signer = true ∨ a.writable = false) :
    freshReference args s = ⟨s,[],.error (.program 0x41532035)⟩ := by
  rcases h with h | h | h | h <;> simp [freshReference,Reference.error,h]
#print axioms fresh_header_reject
end PCC
