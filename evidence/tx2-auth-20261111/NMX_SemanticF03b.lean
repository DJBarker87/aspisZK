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
import NMX_SemanticF04
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF03b
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e040 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p040 pool outputLane laneAccount master masterKey checkpoint checkpointKey))
  (NMX_CB03.r040 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey)) := by
 unfold NMX_SF03.p040 NMX_CB03.r040
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.bytes id
 · exact NMX_CommandTransport.data owners ln rn laneAccount
 · intro laneBytes
   exact NMX_SemanticF04.e041 owners ln rn L D lanePacket pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes
#print axioms e040

theorem e039 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p039 pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda))
  (NMX_CB03.r039 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) (id wrongCheckpointPda)) := by
 unfold NMX_SF03.p039 NMX_CB03.r039
 rw [NMX_DenoteStep.check]
 apply NMX_CheckTransport.step
 exact NMX_SemanticF03b.e040 owners ln rn L D lanePacket pool outputLane laneAccount master masterKey checkpoint checkpointKey
#print axioms e039

theorem e038 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p038 pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey))
  (NMX_CB03.r038 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key derivedCheckpoint) (NMX_Carrier.key checkpointKey)) := by
 unfold NMX_SF03.p038 NMX_CB03.r038
 unfold NMX_SourceProgram.raw
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)
   simp only [decide_not,NMX_KeyCarrier.key_equal]
   exact NMX_HeterogeneousPrimitives.pure id _
 · intro wrongCheckpointPda
   exact NMX_SemanticF03b.e039 owners ln rn L D lanePacket pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda
#print axioms e038

theorem e037 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p037 pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint))
  (NMX_CB03.r037 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key derivedCheckpoint)) := by
 unfold NMX_SF03.p037 NMX_CB03.r037
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.key checkpointAccount.key
 · intro checkpointKey
   exact NMX_SemanticF03b.e038 owners ln rn L D lanePacket pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey
#print axioms e037

theorem e036 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p036 pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds))
  (NMX_CB03.r036 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) ((fun x => x.val.map NMX_Carrier.bytes) checkpointSeeds)) := by
 unfold NMX_SF03.p036 NMX_CB03.r036
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_CommandTransport.pda owners ln rn checkpointSeeds pool
 · intro derivedCheckpoint
   exact NMX_SemanticF03b.e037 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint
#print axioms e036
end NMX_SemanticF03b
end
