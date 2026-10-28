import NDO_JHb_AccountReads
import NDO_JHb_Owners
import JHd_KeyStd
import NDO_JHb_CheckpointGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHd_NativeGuards
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHb_World
open _root_.AdapterRw
attribute [local irreducible] e1 e2

theorem flags (a x y : Nat) :
    (e2.snapshot a x y).is_signer=false ∧ (e2.snapshot a x y).is_writable=false ∧
      (e2.snapshot a x y).executable=false := by
  unfold e2
  exact ⟨rfl,rfl,rfl⟩
#print axioms flags

theorem pool_compare (base : Ops) : core.cmp.impls.PartialEqShared.ne
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (JHd_KeyStd.install base))
    JHb_Programs.pool JHb_Programs.pool=ok false := by rfl
#print axioms pool_compare

theorem master (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_KeyStd.install base) (e2.snapshot 1 384 384) JHb_Programs.pool=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_account r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHb_Owners.master,bind_tc_ok]
  unfold r1_pool_adapter.readonly_meta_ok
  rw [pool_compare,bind_tc_ok]
  simp only [(flags 1 384 384).1,(flags 1 384 384).2.1,(flags 1 384 384).2.2]
  rfl
#print axioms master

theorem forest (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_KeyStd.install base) (e2.snapshot 2 192 192) JHb_Programs.pool=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_account r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHb_Owners.forest,bind_tc_ok]
  unfold r1_pool_adapter.readonly_meta_ok
  rw [pool_compare,bind_tc_ok]
  simp only [(flags 2 192 192).1,(flags 2 192 192).2.1,(flags 2 192 192).2.2]
  rfl
#print axioms forest

theorem lane (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_KeyStd.install base) (e2.snapshot 3 768 768) JHb_Programs.pool=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_account r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHb_Owners.lane,bind_tc_ok]
  unfold r1_pool_adapter.readonly_meta_ok
  rw [pool_compare,bind_tc_ok]
  simp only [(flags 3 768 768).1,(flags 3 768 768).2.1,(flags 3 768 768).2.2]
  rfl
#print axioms lane

theorem checkpoint (base : Ops) : r1_pool_adapter.owned.require_verifier_checkpoint
    (JHd_KeyStd.install base) (e2.snapshot 6 1768 1768) CPH_Program.verifier false=ok (.Ok ()) := by
  have compare : core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (JHd_KeyStd.install base))
      CPH_Program.verifier CPH_Program.verifier=ok false := by rfl
  have len : r1_pool_adapter.owned.OwnedAccount.data_len (JHd_KeyStd.install base)
      (e2.snapshot 6 1768 1768)=ok (.Ok 1768#usize) := by
    unfold r1_pool_adapter.owned.OwnedAccount.data_len
    rw [JHb_CheckpointGuard.length]
    rfl
  unfold r1_pool_adapter.owned.require_verifier_checkpoint r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHb_Owners.checkpoint,bind_tc_ok,compare,bind_tc_ok]
  simp only [(flags 6 1768 1768).1,(flags 6 1768 1768).2.1,(flags 6 1768 1768).2.2]
  simp only [show (false != false)=false from rfl,Bool.false_eq_true,ite_false]
  rw [len,bind_tc_ok]
  rfl
#print axioms checkpoint
end AspisR1.JHd_NativeGuards
end
