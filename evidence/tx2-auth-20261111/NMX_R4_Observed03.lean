import NMX_R4_CallContext
import NMX_R4_PdaObservation
import NMX_R4_CallScript03
import NMX_Fold03
import NMX_R4_Observed04
set_option autoImplicit false
noncomputable section
namespace NMX_R4_Observed03
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallRun NMX_R4_CallContext

theorem e040 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript03.t040 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p040 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey) := by
 unfold NMX_R4_CallScript03.t040 NMX_Fold03.p040
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.data laneAccount)) (fun reply => NMX_R4_TryObservation.after reply (fun laneBytes => NMX_R4_CallScript04.t041 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes))) = _
 apply NMX_R4_ObservedStep.child
 intro laneBytes
 exact NMX_R4_Observed04.e041 c pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes
#print axioms e040

theorem e039 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) :
 observe c (NMX_R4_CallScript03.t039 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p039 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda) := by
 unfold NMX_R4_CallScript03.t039 NMX_Fold03.p039
 cases condition : (wrongCheckpointPda) with
 | true => rfl
 | false => exact NMX_R4_Observed03.e040 c pool outputLane laneAccount master masterKey checkpoint checkpointKey
#print axioms e039

theorem e038 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript03.t038 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p038 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey) := by
 unfold NMX_R4_CallScript03.t038 NMX_Fold03.p038
 apply NMX_R4_ObservedStep.scalar
 intro wrongCheckpointPda
 exact NMX_R4_Observed03.e039 c pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda
#print axioms e038

theorem e037 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript03.t037 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p037 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint) := by
 unfold NMX_R4_CallScript03.t037 NMX_Fold03.p037
 apply NMX_R4_ObservedStep.scalar
 intro checkpointKey
 exact NMX_R4_Observed03.e038 c pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey
#print axioms e037

theorem e036 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) :
 observe c (NMX_R4_CallScript03.t036 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p036 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds) := by
 unfold NMX_R4_CallScript03.t036 NMX_Fold03.p036
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.pda checkpointSeeds pool) (fun reply => NMX_R4_PdaObservation.after r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError reply (fun derivedCheckpoint => NMX_R4_CallScript03.t037 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint))) = _
 apply NMX_R4_PdaObservation.step
 · rfl
 intro derivedCheckpoint
 exact NMX_R4_Observed03.e037 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint
#print axioms e036

theorem e035 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 observe c (NMX_R4_CallScript03.t035 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p035 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint) := by
 unfold NMX_R4_CallScript03.t035 NMX_Fold03.p035
 apply NMX_R4_ObservedStep.scalar
 intro checkpointMasterSeed
 simp only [NMX_R4_CallLaws.observed_scalar,NMX_R3_RegistryRun.scalar,NMX_R2_Observation.bind]
 let sequenceSeed := Array.to_slice (core.num.U64.to_le_bytes checkpoint.payload.checkpoint_sequence)
 let checkpointBump := Array.to_slice (Array.make 1#usize [checkpoint.payload.bump])
 let checkpointSeeds := Array.to_slice (Array.make 4#usize [
   r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,checkpointMasterSeed,sequenceSeed,checkpointBump])
 exact NMX_R4_Observed03.e036 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds
#print axioms e035

theorem e034 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) :
 observe c (NMX_R4_CallScript03.t034 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p034 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment) := by
 unfold NMX_R4_CallScript03.t034 NMX_Fold03.p034
 cases condition : (wrongDeployment) with
 | true => rfl
 | false => exact NMX_R4_Observed03.e035 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e034

theorem e033 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 observe c (NMX_R4_CallScript03.t033 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p033 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint) := by
 unfold NMX_R4_CallScript03.t033 NMX_Fold03.p033
 apply NMX_R4_ObservedStep.scalar
 intro wrongDeployment
 exact NMX_R4_Observed03.e034 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment
#print axioms e033

theorem e032 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) :
 observe c (NMX_R4_CallScript03.t032 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p032 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster) := by
 unfold NMX_R4_CallScript03.t032 NMX_Fold03.p032
 cases condition : (wrongCheckpointMaster) with
 | true => rfl
 | false => exact NMX_R4_Observed03.e033 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e032

theorem e031 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) :
 observe c (NMX_R4_CallScript03.t031 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold03.p031 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes) := by
 unfold NMX_R4_CallScript03.t031 NMX_Fold03.p031
 apply NMX_R4_ObservedStep.scalar
 intro wrongCheckpointMaster
 exact NMX_R4_Observed03.e032 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster
#print axioms e031
end NMX_R4_Observed03
end
