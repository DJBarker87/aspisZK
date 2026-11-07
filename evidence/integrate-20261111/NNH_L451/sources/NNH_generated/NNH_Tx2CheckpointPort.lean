import NNH_Tx2ModelSlots
import NNH_ModelCheckpoint
set_option autoImplicit false
noncomputable section
namespace NNH_Tx2CheckpointPort
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

theorem reinstall (base : Ops) (env : RSL.Env) :
 NGL_CheckpointModel.install (NNH_Tx2ModelSlots.install base env)=NNH_Tx2ModelSlots.install base env := by
 unfold NGL_CheckpointModel.install NNH_Tx2ModelSlots.install
 congr 1
 funext v
 cases v <;> rfl

theorem value (base : Ops) (env : RSL.Env) (a : r1_pool_adapter.owned.OwnedAccount)
 (program : solana_pubkey.Pubkey) (writable : Bool) :
 outer (reply id)
 (r1_pool_adapter.owned.require_verifier_checkpoint (NNH_Tx2ModelSlots.install base env) a program writable)=
 .ok (NNH_ReturnedClone.checkpointValue (account a) (key program) writable) := by
 have h := NNH_ModelCheckpoint.value (NNH_Tx2ModelSlots.install base env) a program writable
 rw [reinstall] at h
 exact h
#print axioms reinstall
#print axioms value
end NNH_Tx2CheckpointPort
