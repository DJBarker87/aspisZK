import NMX_ReadonlyCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_CheckpointCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_Carrier NMX_ObserveResult
attribute [local instance] Classical.propDecidable
/-- Pure typed packet comparison, with full deferred errors preserved. -/
theorem reply (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey) :
 NMX_Carrier.reply (fun u : Unit => u) (NGL_CheckpointModel.reply a program false) =
 RSL.verifierCheckpoint (account a) (key program) false := by
 unfold NGL_CheckpointModel.reply RSL.verifierCheckpoint
 simp only [account,decide_not,NMX_KeyCarrier.key_equal]
 cases h : decide (a.owner = program) <;> cases a.is_signer <;>
  cases a.executable <;> cases a.is_writable <;>
  simp only [h,Bool.not_false,Bool.not_true,Bool.false_or,Bool.true_or,
   Bool.or_false,Bool.or_true,Bool.false_eq_true,↓reduceIte,Bool.false_bne,
   NMX_Carrier.reply,NMX_Carrier.error]
 all_goals
  cases length : a.length with
  | Err e => rfl
  | Ok n =>
    by_cases fits : n.val = 1768
    · have same : n = 1768#usize := UScalar.eq_of_val_eq fits
      simp [same,RSL.OwnedAccount.data_len,account,length,RSL.CHECKPOINT_BYTES,
       NMX_Carrier.reply]
    · have different : n ≠ 1768#usize := by
        intro same;apply fits;exact congrArg UScalar.val same
      simp [different,fits,RSL.OwnedAccount.data_len,account,length,RSL.CHECKPOINT_BYTES,
       NMX_Carrier.reply,NMX_Carrier.error]

/-- CLOSED checkpoint packet at the actual final account and program,false;
the child-domain clause is named and unchanged. -/
theorem checkpoint (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (program : solana_pubkey.Pubkey) (domain : NGL_LengthCarrier.domain a.length) :
 observe (fun u : Unit => u)
  (r1_pool_adapter.owned.require_verifier_checkpoint (NMX_LeafInstall.install ops) a program false) =
 ⟨.ret (RSL.verifierCheckpoint (account a) (key program) false),[]⟩ := by
 rw [NHJ_CheckpointPacket.substitute ops a program false domain]
 have encoded : NHJ_CheckpointPacket.G a program false (NHJ_CheckpointPacket.encode a.length) =
   NGL_CheckpointModel.reply a program false := by
  unfold NHJ_CheckpointPacket.G
  rw [NHJ_CheckpointPacket.decode_encode a.length domain]
  rfl
 rw [encoded]
 exact congrArg (fun r => RSL.Obs.mk (.ret r) []) (reply a program)
#print axioms reply
#print axioms checkpoint
end NMX_CheckpointCarrier
end
