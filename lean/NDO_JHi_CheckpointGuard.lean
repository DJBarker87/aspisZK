import NDO_JHb_Owners
import NDO_JHg_AuditWorld
import JHd_KeyStd
import JHb_CheckpointSize
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_CheckpointGuard
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHg_World
open _root_.AdapterRw
attribute [local irreducible] e1 e2 JFx_NativeBytes.checkpoint

theorem length : (e2.snapshot 6 1768 1768).length=.Ok 1768#usize := by
  change core.result.Result.Ok (Slice.len (e2.buffers (e2.handles 6).1))=_
  rw [JHg_AuditWorld.checkpoint]
  congr 1
  apply UScalar.eq_of_val_eq
  unfold JFx_NativeBytes.checkpoint
  exact JFx_NativeBytes.checkpointBytes_length
#print axioms length

theorem data_len (base : Ops) :
    r1_pool_adapter.owned.OwnedAccount.data_len (JHd_KeyStd.install base)
      (e2.snapshot 6 1768 1768)=ok (.Ok 1768#usize) := by
  unfold r1_pool_adapter.owned.OwnedAccount.data_len
  rw [length]
  rfl
#print axioms data_len

theorem source (base : Ops) :
    r1_pool_adapter.owned.require_verifier_checkpoint (JHd_KeyStd.install base)
      (e2.snapshot 6 1768 1768) CPH_Program.verifier false=ok (.Ok ()) := by
  have key : core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (JHd_KeyStd.install base))
      CPH_Program.verifier CPH_Program.verifier=ok false := by rfl
  unfold r1_pool_adapter.owned.require_verifier_checkpoint r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHg_AuditWorld.owner,JHb_Owners.checkpoint,bind_tc_ok,key,bind_tc_ok]
  have flags : (e2.snapshot 6 1768 1768).is_signer=false ∧
      (e2.snapshot 6 1768 1768).executable=false ∧ (e2.snapshot 6 1768 1768).is_writable=false := by
    unfold e2
    exact ⟨rfl,rfl,rfl⟩
  simp only [flags.1,flags.2.1,flags.2.2,Bool.false_eq_true,ite_false,show (false != false)=false from rfl]
  rw [data_len,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHi_CheckpointGuard
end
