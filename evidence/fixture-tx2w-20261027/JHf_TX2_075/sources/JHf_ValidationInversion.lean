import JHf_ReconstructionSlot
import JHd_Validation
import JHb_S2K_StatementAdmission
set_option autoImplicit false
namespace AspisR1.JHf_ValidationInversion
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
attribute [local irreducible] r1_pool_adapter.owned.authenticate_asq8_accounts
  r1_pool_adapter.owned.OwnedAccount.data

theorem source (ops : Ops) (verifier : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
    (slot : core.result.Result U64 solana_program_error.ProgramError)
    (out : r1_pool_adapter.ValidatedAsqa)
    (accepted : r1_pool_adapter.owned.validate_asq8 ops verifier accounts data slot=ok (.Ok out)) :
    ∃ request authenticated candidate pool lane current,
      ops.op23 data=ok (.Ok request) ∧
      r1_pool_adapter.owned.authenticate_asq8_accounts ops verifier accounts pool lane current=
        ok (.Ok authenticated) ∧
      ops.op52 request authenticated candidate=ok (.Ok out.statement) := by
  unfold r1_pool_adapter.owned.validate_asq8 at accepted
  repeat' first
  | (solve | exact ⟨_,_,_,_,_,_,by assumption,by assumption,by assumption⟩)
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | s2k_unbool
  | split at accepted
  | cases accepted
#print axioms source
end AspisR1.JHf_ValidationInversion
