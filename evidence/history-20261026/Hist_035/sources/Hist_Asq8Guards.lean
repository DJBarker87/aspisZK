import S2W_EntryPrivileges
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_Asq8Guards
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw.Cuts
attribute [local irreducible]
  AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  AdapterRw.r1_pool_adapter.owned.require_readonly_account
  AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry

/-- The ASQ8 path authenticates the Pool forest checkpoint and the separate
verifier checkpoint at different slots and under different program owners. -/
theorem guards (ops : AdapterRw.Ops) (verifier pool : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (lane : U8) (slot : U64)
    (out : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (accepted : AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts ops verifier accounts pool lane slot = ok (.Ok out)) :
    ∃ master forest selected checkpoint,
      Slice.index_usize accounts 1#usize = ok master ∧
      Slice.index_usize accounts 2#usize = ok forest ∧
      Slice.index_usize accounts 3#usize = ok selected ∧
      Slice.index_usize accounts 6#usize = ok checkpoint ∧
      AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops checkpoint verifier false = ok (.Ok ()) ∧
      AdapterRw.r1_pool_adapter.owned.require_readonly_account ops master pool = ok (.Ok ()) ∧
      AdapterRw.r1_pool_adapter.owned.require_readonly_account ops forest pool = ok (.Ok ()) ∧
      AdapterRw.r1_pool_adapter.owned.require_readonly_account ops selected pool = ok (.Ok ()) := by
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

#print axioms guards
end AspisR1.Hist_Asq8Guards
end
