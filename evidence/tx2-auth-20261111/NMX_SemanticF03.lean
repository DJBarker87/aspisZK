import NMX_SF03
import NMX_CB03
import NMX_DenoteStep
import NMX_BoxCommands
import NMX_CommandTransport
import NMX_IndexTransport
import NMX_ScalarBne
import NMX_ArrayEqualityCarrier
import NMX_SemanticF04
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF03
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e040 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p040 pool outputLane laneAccount master masterKey checkpoint checkpointKey))
  (NMX_CB03.r040 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey)) := by
 unfold NMX_SF03.p040 NMX_CB03.r040
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind bytes id
 · fail "Unimplemented carrier step"
 · intro laneBytes
   exact NMX_SemanticF04.e041 owners ln rn L D lanePacket registryPacket pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes
#print axioms e040

theorem e039 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p039 pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda))
  (NMX_CB03.r039 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) (id wrongCheckpointPda)) := by
 unfold NMX_SF03.p039 NMX_CB03.r039
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e038 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p038 pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey))
  (NMX_CB03.r038 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key derivedCheckpoint) (key checkpointKey)) := by
 unfold NMX_SF03.p038 NMX_CB03.r038
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro wrongCheckpointPda
   exact NMX_SemanticF03.e039 owners ln rn L D lanePacket registryPacket pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda
#print axioms e038

theorem e037 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p037 pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint))
  (NMX_CB03.r037 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key derivedCheckpoint)) := by
 unfold NMX_SF03.p037 NMX_CB03.r037
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key checkpointAccount.key
 · intro checkpointKey
   exact NMX_SemanticF03.e038 owners ln rn L D lanePacket registryPacket pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey
#print axioms e037

theorem e036 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p036 pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds))
  (NMX_CB03.r036 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) ((fun x => x.val.map bytes) checkpointSeeds)) := by
 unfold NMX_SF03.p036 NMX_CB03.r036
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · fail "Unimplemented carrier step"
 · intro derivedCheckpoint
   exact NMX_SemanticF03.e037 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint
#print axioms e036

theorem e035 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p035 pool outputLane checkpointAccount laneAccount master masterKey checkpoint))
  (NMX_CB03.r035 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint)) := by
 unfold NMX_SF03.p035 NMX_CB03.r035
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind bytes id
 · exact NMX_HeterogeneousPrimitives.pure bytes (Array.to_slice masterKey)
 · intro checkpointMasterSeed
   exact NMX_SemanticF03.e036 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds
#print axioms e035

theorem e034 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p034 pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment))
  (NMX_CB03.r034 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (id wrongDeployment)) := by
 unfold NMX_SF03.p034 NMX_CB03.r034
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e033 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p033 pool outputLane checkpointAccount laneAccount master masterKey checkpoint))
  (NMX_CB03.r033 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint)) := by
 unfold NMX_SF03.p033 NMX_CB03.r033
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro wrongDeployment
   exact NMX_SemanticF03.e034 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment
#print axioms e033

theorem e032 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p032 pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster))
  (NMX_CB03.r032 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (id wrongCheckpointMaster)) := by
 unfold NMX_SF03.p032 NMX_CB03.r032
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e031 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF03.p031 pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes))
  (NMX_CB03.r031 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointMasterBytes)) := by
 unfold NMX_SF03.p031 NMX_CB03.r031
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro wrongCheckpointMaster
   exact NMX_SemanticF03.e032 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster
#print axioms e031
end NMX_SemanticF03
end
