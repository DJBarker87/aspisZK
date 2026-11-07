import NNH_ModelLeafPorts
import NNH_ReturnedClone
import NGL_CheckpointModel
set_option autoImplicit false
noncomputable section
namespace NNH_ModelCheckpoint
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem length_compare (x : Usize) :
 (x != 1768#usize)=(x.val != RSL.CHECKPOINT_BYTES) := by
 apply Bool.eq_iff_iff.mpr
 simp only [bne_iff_ne,ne_eq]
 apply not_congr
 constructor
 · intro h; exact congrArg UScalar.val h
 · intro h; exact UScalar.eq_of_val_eq h

theorem value (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (program : solana_pubkey.Pubkey) (writable : Bool) :
 outer (reply id)
 (r1_pool_adapter.owned.require_verifier_checkpoint (NGL_CheckpointModel.install ops) a program writable)=
 .ok (NNH_ReturnedClone.checkpointValue (account a) (key program) writable) := by
 rw [NGL_CheckpointModel.result]
 unfold NGL_CheckpointModel.reply NNH_ReturnedClone.checkpointValue
 have hk : decide (key a.owner = key program)=decide (a.owner=program) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact key_eq_iff a.owner program
 simp only [account,decide_not]
 rw [hk]
 split
 · rfl
 · cases h : a.length with
   | Err e => simp only [h,outer,reply,NND_Returned.ebind]; rfl
   | Ok n =>
     simp only [h,outer,reply,NND_Returned.ebind]
     rw [length_compare]
     split <;> rfl
#print axioms length_compare
#print axioms value
end NNH_ModelCheckpoint
