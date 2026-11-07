import PCF_Payer
import PCF_Token
set_option autoImplicit false
namespace PCM_Inst_AccountSource
open Aeneas Aeneas.Std
/-- Exact CLOSED source-carrier models; PCM/RSL cell and error adapters remain
named obligations. No caller may replace this equality by an arbitrary relation. -/
abbrev PayerArgs := (Nat × Nat) × PCA.PCA_State
def payerModel (a : PayerArgs) := PCA.payerSystemReference a.1 a.2
def payerLaw (a : PayerArgs) (o : PCA.Execution Unit) : Prop := True ∧ o = payerModel a
abbrev TokenArgs := Nat × PCA.PCA_State
def tokenModel (a : TokenArgs) := PCA.tokenProgramReference a.1 a.2

def tokenLaw (a : TokenArgs) (o : PCA.Execution Unit) : Prop := True ∧ o = tokenModel a

theorem payer_graph (a : PayerArgs) (o : PCA.Execution Unit) :
    payerLaw a o ↔ True ∧ o = payerModel a := Iff.rfl

theorem token_graph (a : TokenArgs) (o : PCA.Execution Unit) :
    tokenLaw a o ↔ True ∧ o = tokenModel a := Iff.rfl

theorem payer_native (args : Nat × Nat) (s : PCA.PCA_State) :
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
          else .error (.program (UInt64.ofNat out.val))⟩ := PCF_Payer.result_state_effects args s
theorem token_native (account : Nat) (s : PCA.PCA_State) :
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
          else .error (.program (UInt64.ofNat out.val))⟩ := PCF_Token.result_state_effects account s
#print axioms payer_graph
#print axioms token_graph
#print axioms payer_native
#print axioms token_native
end PCM_Inst_AccountSource
