import NMX_SF00
import NMX_CB00
import NMX_DenoteStep
import NMX_CommandTransport
import NMX_RegistryTransport
import NMX_CheckTransport
import NMX_SeedFrames
import NMX_ScalarBne
import NMX_ArrayEqualityCarrier
import NMX_IndexTransport
import NMX_SemanticF03b
import NMX_U64Carrier
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF03a
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e035 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p035 pool outputLane checkpointAccount laneAccount master masterKey checkpoint))
  (NMX_CB03.r035 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint)) := by
 unfold NMX_SF03.p035 NMX_CB03.r035
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.bytes id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.bytes (Array.to_slice masterKey)
 · intro checkpointMasterSeed
   let sequenceSeed := Array.to_slice (core.num.U64.to_le_bytes checkpoint.payload.checkpoint_sequence)
   let checkpointBump := Array.to_slice (Array.make 1#usize [checkpoint.payload.bump])
   let checkpointSeeds := Array.to_slice (Array.make 4#usize [
     r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,checkpointMasterSeed,sequenceSeed,checkpointBump])
   simpa only [checkpointSeeds,sequenceSeed,checkpointBump,NMX_SeedFrames.checkpoint,NMX_SeedFrames.single,NMX_U64Carrier.value,NMX_Carrier.checkpoint] using (NMX_SemanticF03b.e036 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds)
#print axioms e035

theorem e034 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p034 pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment))
  (NMX_CB03.r034 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (id wrongDeployment)) := by
 unfold NMX_SF03.p034 NMX_CB03.r034
 rw [NMX_DenoteStep.check]
 apply NMX_CheckTransport.step
 exact NMX_SemanticF03a.e035 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e034

theorem e033 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p033 pool outputLane checkpointAccount laneAccount master masterKey checkpoint))
  (NMX_CB03.r033 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint)) := by
 unfold NMX_SF03.p033 NMX_CB03.r033
 unfold NMX_SourceProgram.raw
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)
   rw [NMX_ArrayEqualityCarrier.array_ne]
   exact NMX_HeterogeneousPrimitives.pure id _
 · intro wrongDeployment
   exact NMX_SemanticF03a.e034 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment
#print axioms e033

theorem e032 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p032 pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster))
  (NMX_CB03.r032 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (id wrongCheckpointMaster)) := by
 unfold NMX_SF03.p032 NMX_CB03.r032
 rw [NMX_DenoteStep.check]
 apply NMX_CheckTransport.step
 exact NMX_SemanticF03a.e033 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e032

theorem e031 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p031 pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes))
  (NMX_CB03.r031 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointMasterBytes)) := by
 unfold NMX_SF03.p031 NMX_CB03.r031
 unfold NMX_SourceProgram.raw
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)
   rw [NMX_ArrayEqualityCarrier.array_ne]
   exact NMX_HeterogeneousPrimitives.pure id _
 · intro wrongCheckpointMaster
   exact NMX_SemanticF03a.e032 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster
#print axioms e031
end NMX_SemanticF03a
end
