import NMX_BindCongruence
import NMX_PdaMap
import NMX_Actual03
import NMX_Fold03
import NMX_Match04
set_option autoImplicit false
noncomputable section
namespace NMX_Match03
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

/-- Actual emitted occurrence 40; complete arbitrary reply/control arms. -/
theorem e040 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_Fold03.v040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey =
 NMX_Actual03.t040 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey := by
 unfold NMX_Fold03.v040 NMX_Actual03.t040
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok laneBytes =>
   exact NMX_Match04.e041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes
#print axioms e040

/-- Actual emitted occurrence 39; complete arbitrary reply/control arms. -/
theorem e039 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) :
 NMX_Fold03.v039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda =
 NMX_Actual03.t039 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey wrongCheckpointPda := by
 unfold NMX_Fold03.v039 NMX_Actual03.t039
 by_cases condition : (wrongCheckpointPda) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match03.e040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey
#print axioms e039

/-- Actual emitted occurrence 38; complete arbitrary reply/control arms. -/
theorem e038 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_Fold03.v038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey =
 NMX_Actual03.t038 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload derivedCheckpoint checkpointKey := by
 unfold NMX_Fold03.v038 NMX_Actual03.t038
 apply NMX_BindCongruence.step
 intro wrongCheckpointPda
 exact NMX_Match03.e039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda
#print axioms e038

/-- Actual emitted occurrence 37; complete arbitrary reply/control arms. -/
theorem e037 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) :
 NMX_Fold03.v037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint =
 NMX_Actual03.t037 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload derivedCheckpoint := by
 unfold NMX_Fold03.v037 NMX_Actual03.t037
 apply NMX_BindCongruence.step
 intro checkpointKey
 exact NMX_Match03.e038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey
#print axioms e037

/-- Actual emitted occurrence 36; complete arbitrary reply/control arms. -/
theorem e036 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) :
 NMX_Fold03.v036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds =
 NMX_Actual03.t036 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload checkpointSeeds := by
 unfold NMX_Fold03.v036 NMX_Actual03.t036
 rw [NMX_PdaMap.try_bind]
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok derivedCheckpoint =>
   exact NMX_Match03.e037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint
#print axioms e036

/-- Actual emitted occurrence 35; complete arbitrary reply/control arms. -/
theorem e035 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Fold03.v035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint =
 NMX_Actual03.t035 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload := by
 unfold NMX_Fold03.v035 NMX_Actual03.t035
 apply NMX_BindCongruence.step
 intro checkpointMasterSeed
 let sequenceSeed := Array.to_slice (core.num.U64.to_le_bytes checkpoint.payload.checkpoint_sequence)
 let checkpointBump := Array.to_slice (Array.make 1#usize [checkpoint.payload.bump])
 let checkpointSeeds := Array.to_slice (Array.make 4#usize [
   r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,checkpointMasterSeed,sequenceSeed,checkpointBump])
 exact NMX_Match03.e036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds
#print axioms e035

/-- Actual emitted occurrence 34; complete arbitrary reply/control arms. -/
theorem e034 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) :
 NMX_Fold03.v034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment =
 NMX_Actual03.t034 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload wrongDeployment := by
 unfold NMX_Fold03.v034 NMX_Actual03.t034
 by_cases condition : (wrongDeployment) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match03.e035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e034

/-- Actual emitted occurrence 33; complete arbitrary reply/control arms. -/
theorem e033 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Fold03.v033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint =
 NMX_Actual03.t033 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload := by
 unfold NMX_Fold03.v033 NMX_Actual03.t033
 apply NMX_BindCongruence.step
 intro wrongDeployment
 exact NMX_Match03.e034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment
#print axioms e033

/-- Actual emitted occurrence 32; complete arbitrary reply/control arms. -/
theorem e032 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) :
 NMX_Fold03.v032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster =
 NMX_Actual03.t032 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload wrongCheckpointMaster := by
 unfold NMX_Fold03.v032 NMX_Actual03.t032
 by_cases condition : (wrongCheckpointMaster) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match03.e033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e032

/-- Actual emitted occurrence 31; complete arbitrary reply/control arms. -/
theorem e031 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) :
 NMX_Fold03.v031 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes =
 NMX_Actual03.t031 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload checkpointMasterBytes := by
 unfold NMX_Fold03.v031 NMX_Actual03.t031
 apply NMX_BindCongruence.step
 intro wrongCheckpointMaster
 exact NMX_Match03.e032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster
#print axioms e031
end NMX_Match03
end
