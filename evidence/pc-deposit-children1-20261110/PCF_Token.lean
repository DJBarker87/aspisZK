import PCF_AccountLaws
import PCA_ValidatorReferences
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_Token

theorem result_state_effects (account : Nat) (s : PCA.PCA_State) :
    ∃ out : U32,
      PCF_AccountRef.token_reference
        ((s.loans.state.accounts account).key == PCA.token_program)
        (s.loans.state.accounts account).executable
        (s.loans.state.accounts account).signer
        (s.loans.state.accounts account).writable
        ((s.loans.state.accounts account).owner == PCA.bpf_loader)
        ((s.loans.state.accounts account).owner == PCA.bpf_loader_upgradeable)
        ((s.loans.state.accounts account).owner == PCA.loader_v4) = .ok out ∧
      PCA.tokenProgramReference account s =
        ⟨s, [], if out.val = 0 then .ok ()
          else .error (.program (UInt64.ofNat out.val))⟩ := by
  let a := s.loans.state.accounts account
  refine ⟨PCF_AccountLaws.tokenModel (a.key == PCA.token_program)
      a.executable a.signer a.writable (a.owner == PCA.bpf_loader)
      (a.owner == PCA.bpf_loader_upgradeable) (a.owner == PCA.loader_v4),
    PCF_AccountLaws.token _ _ _ _ _ _ _, ?_⟩
  simp only [PCA.tokenProgramReference, PCA.supportedLoader, PCF_AccountLaws.tokenModel]
  split_ifs <;> first | rfl | (exfalso; scalar_tac)

#print axioms result_state_effects
end PCF_Token
