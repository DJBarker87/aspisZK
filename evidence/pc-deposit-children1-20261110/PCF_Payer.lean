import PCF_AccountLaws
import PCA_ValidatorReferences
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_Payer

theorem result_state_effects (args : Nat × Nat) (s : PCA.PCA_State) :
    ∃ out : U32,
      PCF_AccountRef.payer_reference
        (s.loans.state.accounts args.1).signer
        (s.loans.state.accounts args.1).writable
        (s.loans.state.accounts args.1).executable
        ((s.loans.state.accounts args.1).owner == PCA.system_program)
        ((s.loans.state.accounts args.2).key == PCA.system_program)
        ((s.loans.state.accounts args.2).owner == PCA.native_loader)
        (s.loans.state.accounts args.2).executable
        (s.loans.state.accounts args.2).signer
        (s.loans.state.accounts args.2).writable = .ok out ∧
      PCA.payerSystemReference args s =
        ⟨s, [], if out.val = 0 then .ok ()
          else .error (.program (UInt64.ofNat out.val))⟩ := by
  let p := s.loans.state.accounts args.1
  let q := s.loans.state.accounts args.2
  refine ⟨PCF_AccountLaws.payerModel p.signer p.writable p.executable
      (p.owner == PCA.system_program) (q.key == PCA.system_program)
      (q.owner == PCA.native_loader) q.executable q.signer q.writable,
    PCF_AccountLaws.payer _ _ _ _ _ _ _ _ _, ?_⟩
  change PCA.payerSystemReference args s = _
  simp only [PCA.payerSystemReference, PCF_AccountLaws.payerModel]
  split_ifs <;> first | rfl | (exfalso; scalar_tac)

#print axioms result_state_effects
end PCF_Payer
