import NDO_JHe_SdkReads
import NDO_JHe_ZeroGate
import JHb_GuardStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SdkCheckpoint
open Aeneas Aeneas.Std Result S2W_D189Entry
open _root_.AdapterRw
abbrev e := JHb_World.e1
attribute [local irreducible] JHb_World.e1

theorem zero : r1_pool_adapter.owned.require_zero JHe_SdkReads.checkpoint=ok (.Ok ()) := by
  apply JHe_ZeroGate.source
  · intro b member
    exact List.eq_of_mem_replicate member
  · change (List.replicate 1768 (0#u8)).length≤4096
    rw [List.length_replicate]
    decide
#print axioms zero

theorem source (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_verifier_checkpoint (JHe_Natives.sdk base stage)
      (e.snapshot 2 1768 1768) CPH_Program.verifier true=ok (.Ok ()) := by
  have key : core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (JHe_Natives.sdk base stage))
      CPH_Program.verifier CPH_Program.verifier=ok false := by
    change core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (Hist_Authority.install (JHe_Natives.sdk base stage))) _ _=_
    exact JHb_GuardStd.key_ne_self _ _
  unfold r1_pool_adapter.owned.require_verifier_checkpoint r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHc_CorrectedOwnership.checkpoint_owner,bind_tc_ok,key,bind_tc_ok]
  have flags : (e.snapshot 2 1768 1768).is_signer=false ∧
      (e.snapshot 2 1768 1768).executable=false ∧ (e.snapshot 2 1768 1768).is_writable=true := by
    unfold e JHb_World.e1
    exact ⟨rfl,rfl,rfl⟩
  simp only [flags.1,flags.2.1,flags.2.2,Bool.false_eq_true,if_false,bne_self_eq_false]
  have len : r1_pool_adapter.owned.OwnedAccount.data_len (JHe_Natives.sdk base stage)
      (e.snapshot 2 1768 1768)=ok (.Ok 1768#usize) := by
    unfold r1_pool_adapter.owned.OwnedAccount.data_len
    rw [JHe_SdkReads.length]
    rfl
  rw [len,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHe_SdkCheckpoint
end
