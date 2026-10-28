import NDG_MetadataBridge
set_option autoImplicit false
namespace NDG_AccessLaws
open Aeneas Aeneas.Std Result
open AdapterRw

theorem data_success (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (v : alloc.vec.Vec U8) (h : a.bytes = .Ok v) :
    r1_pool_adapter.owned.OwnedAccount.data ops a = ok (.Ok (alloc.vec.Vec.deref v)) := by
  simp only [r1_pool_adapter.owned.OwnedAccount.data, h]

theorem data_error (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (e : solana_program_error.ProgramError) (h : a.bytes = .Err e)
    (clone : ops.op35 e = ok e) :
    r1_pool_adapter.owned.OwnedAccount.data ops a = ok (.Err e) := by
  simp only [r1_pool_adapter.owned.OwnedAccount.data, h, clone, bind_tc_ok]

theorem readonly_buffer_caller (a : r1_pool_adapter.owned.OwnedAccount) :
    r1_pool_adapter.owned.require_readonly_buffer a =
      (do let b ← NDG_Reference.readonly_buffer_ref a.is_signer a.is_writable a.executable
          ok (NDG_MetadataBridge.liftReadonly b)) := by
  exact (NDG_MetadataBridge.buffer _ _ _).symm

theorem readonly_account_caller (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (expected : solana_pubkey.Pubkey) (different : Bool)
    (comparison : core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) a.owner expected = ok different) :
    r1_pool_adapter.owned.require_readonly_account ops a expected =
      (do let b ← NDG_Reference.readonly_ref different a.is_signer a.is_writable a.executable
          ok (NDG_MetadataBridge.liftReadonly b)) := by
  simp only [r1_pool_adapter.owned.require_readonly_account,
    r1_pool_adapter.owned.OwnedAccount.impl.owner, bind_tc_ok]
  exact (NDG_MetadataBridge.metadata ops _ _ _ _ _ _ comparison).symm

#print axioms data_success
#print axioms data_error
#print axioms readonly_buffer_caller
#print axioms readonly_account_caller
end NDG_AccessLaws
