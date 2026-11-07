import NNH_Tx2ModelSlots
import LIBB_PoolAccounts
set_option autoImplicit false
noncomputable section
namespace NNH_BoxOk
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_Libraries

theorem master (b : Slice U8) (m : RSL.Master)
 (success : L.decodeMaster (bytes b)=some m) :
 ∃ n,NKF_MasterBox.reference b=.ok (.Ok n) ∧ NND_Carrier.master n=m := by
 change LIBB_AccountDecoderReuse.master (bytes b)=some m at success
 rw [LIBB_AccountGraph.master_same] at success
 cases source : NMX_MasterValue.decoded b with
 | Err e => rw [source] at success; cases success
 | Ok n =>
  rw [source] at success
  exact ⟨n,(NMX_MasterValue.source b).trans (congrArg Result.ok source),Option.some.inj success⟩

theorem checkpoint (b : Slice U8) (m : RSL.Checkpoint)
 (success : L.decodeCheckpoint (bytes b)=some m) :
 ∃ n,NKF_CheckpointBox.reference b=.ok (.Ok n) ∧ NND_Carrier.checkpoint n=m := by
 change LIBB_AccountDecoderReuse.checkpoint (bytes b)=some m at success
 rw [LIBB_AccountGraph.checkpoint_same] at success
 cases source : NMX_CheckpointValue.decoded b with
 | Err e => rw [source] at success; cases success
 | Ok n =>
  rw [source] at success
  exact ⟨n,(NMX_CheckpointValue.source b).trans (congrArg Result.ok source),Option.some.inj success⟩
#print axioms master
#print axioms checkpoint
end NNH_BoxOk
