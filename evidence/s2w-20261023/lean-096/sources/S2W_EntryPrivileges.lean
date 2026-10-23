import AdapterRwCuts

/-! Source guards, not an alias/frame hypothesis. Kept under the small
extraction import to avoid elaborating the whole stage1 beneath the final union. -/
set_option autoImplicit false
namespace AspisR1.S2W_EntryPrivileges
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.AdapterRw.Cuts
attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  AdapterRw.r1_pool_adapter.owned.require_zero AdapterRw.first_decoded

theorem guards (ops : AdapterRw.Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : r1_pool_adapter.owned.stage1_owned ops program accounts data = ok (.Ok saved)) :
    ∃ pa pu ca,
      Slice.index_usize accounts 0#usize = ok pa ∧
      Slice.index_usize accounts 1#usize = ok pu ∧
      Slice.index_usize accounts 2#usize = ok ca ∧
      r1_pool_adapter.owned.require_readonly_buffer pa = ok (.Ok ()) ∧
      r1_pool_adapter.owned.require_readonly_buffer pu = ok (.Ok ()) ∧
      r1_pool_adapter.owned.require_verifier_checkpoint ops ca program true = ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.stage1_owned at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

attribute [local reducible] AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint

 theorem readonly (a : Account)
    (accepted : r1_pool_adapter.owned.require_readonly_buffer a = ok (.Ok ())) :
    a.is_writable = false := by
  unfold r1_pool_adapter.owned.require_readonly_buffer r1_pool_adapter.readonly_buffer_meta_ok at accepted
  cases h : a.is_writable <;> simp_all

 theorem writable (ops : AdapterRw.Ops) (a : Account) (program : solana_pubkey.Pubkey)
    (accepted : r1_pool_adapter.owned.require_verifier_checkpoint ops a program true = ok (.Ok ())) :
    a.is_writable = true := by
  unfold r1_pool_adapter.owned.require_verifier_checkpoint at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals aesop (add simp [bne_iff_ne])

 theorem accepted_privileges (ops : AdapterRw.Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : r1_pool_adapter.owned.stage1_owned ops program accounts data = ok (.Ok saved)) :
    ∃ pa pu ca,
      Slice.index_usize accounts 0#usize = ok pa ∧
      Slice.index_usize accounts 1#usize = ok pu ∧
      Slice.index_usize accounts 2#usize = ok ca ∧
      pa.is_writable = false ∧ pu.is_writable = false ∧ ca.is_writable = true := by
  obtain ⟨pa,pu,ca,ip,iu,ic,rp,ru,rc⟩ := guards ops program accounts data saved accepted
  exact ⟨pa,pu,ca,ip,iu,ic,readonly pa rp,readonly pu ru,writable ops ca program rc⟩

#print axioms guards
#print axioms readonly
#print axioms writable
#print axioms accepted_privileges
end AspisR1.S2W_EntryPrivileges
