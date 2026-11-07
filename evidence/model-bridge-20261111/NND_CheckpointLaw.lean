import NND_AccountLaws
import NGL_CheckpointModel
set_option autoImplicit false
noncomputable section
namespace NND_Carrier
open Aeneas Aeneas.Std Result AdapterRw

theorem usize_eq (x y : Usize) : (x = y) ↔ (x.val = y.val) :=
 ⟨congrArg UScalar.val,fun h => UScalar.eq_of_val_eq h⟩

theorem checkpoint_length_compare (x : Usize) :
 (x != 1768#usize) = (x.val != RSL.CHECKPOINT_BYTES) := by
 apply Bool.eq_iff_iff.mpr
 simp only [bne_iff_ne,ne_eq,usize_eq]
 rfl

theorem checkpoint (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (p : solana_pubkey.Pubkey) (w : Bool) :
 outer (reply id)
 (r1_pool_adapter.owned.require_verifier_checkpoint (NGL_CheckpointModel.install ops) a p w) =
 ok (RSL.verifierCheckpoint (account a) (key p) w) := by
 classical
 rw [NGL_CheckpointModel.result]
 unfold NGL_CheckpointModel.reply RSL.verifierCheckpoint
 have hk : decide (key a.owner = key p) = decide (a.owner = p) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact key_eq_iff a.owner p
 simp only [account,decide_not]
 rw [hk]
 split
 · rfl
 · cases h : a.length with
   | Err e => simp [h,RSL.OwnedAccount.data_len,outer,reply,account]
   | Ok n =>
     simp only [h,RSL.OwnedAccount.data_len,reply]
     rw [checkpoint_length_compare]
     split <;> rfl

#print axioms usize_eq
#print axioms checkpoint_length_compare
#print axioms checkpoint
end NND_Carrier
