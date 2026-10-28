import NCK_Readonly
import NCK_Getters
set_option autoImplicit false
noncomputable section
namespace NCK_OwnedMeta
open Aeneas Aeneas.Std Result
open AdapterRw.r1_pool_adapter AdapterRw.r1_pool_adapter.owned

theorem buffer_exact (a : OwnedAccount) :
    require_readonly_buffer a =
      ok (if a.is_signer || a.is_writable || a.executable then
        core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData
        else .Ok ()) := NCK_Readonly.buffer_exact _ _ _

theorem account_call (ops : AdapterRw.Ops) (a : OwnedAccount)
    (owner : AdapterRw.solana_pubkey.Pubkey) :
    require_readonly_account ops a owner =
      readonly_meta_ok ops a.owner owner a.is_signer a.is_writable a.executable := rfl

theorem length_ok (ops : AdapterRw.Ops) (a : OwnedAccount) (n : Usize)
    (length : a.length = .Ok n) : OwnedAccount.data_len ops a = ok (.Ok n) := by
  simp [OwnedAccount.data_len, length,
    AdapterRw.core.result.Result.Insts.CoreCloneClone.clone]

#print axioms buffer_exact
#print axioms account_call
#print axioms length_ok
end NCK_OwnedMeta
end
