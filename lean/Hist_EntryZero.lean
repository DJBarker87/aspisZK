import S2W_EntryPrivileges
set_option autoImplicit false
namespace AspisR1.Hist_EntryZero
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.AdapterRw.Cuts
attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  AdapterRw.r1_pool_adapter.owned.require_zero AdapterRw.first_decoded

/-- The zero gate belongs to this actual successful writer; it is not an
independently selected check or an extra writer-admission hypothesis. -/
theorem zero_gate (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data = ok (.Ok saved)) :
    ∃ ca bytes,
      Slice.index_usize accounts 2#usize = ok ca ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops ca = ok (.Ok bytes) ∧
      AdapterRw.r1_pool_adapter.owned.require_zero bytes = ok (.Ok ()) := by
  unfold AdapterRw.r1_pool_adapter.owned.stage1_owned at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

#print axioms zero_gate
end AspisR1.Hist_EntryZero
