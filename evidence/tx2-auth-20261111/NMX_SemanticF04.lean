import NMX_SF04
import NMX_CB04
import NMX_TailIndependent
import NMX_DenoteStep
import NMX_CommandTransport
import NMX_CheckTransport
import NMX_SeedFrames
import NMX_ScalarBne
import NMX_ArrayEqualityCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF04
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e050 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p050 master masterKey checkpoint checkpointKey lane laneKey wrongLanePda))
  (NMX_CB04.r050 (NMX_DecoderLibrary.install L) D ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (NMX_Carrier.key laneKey) (id wrongLanePda)) := by
 unfold NMX_SF04.p050 NMX_CB04.r050
 rw [NMX_DenoteStep.check]
 apply NMX_CheckTransport.step
 exact NMX_TailIndependent.e051 owners ln rn L D master masterKey checkpoint checkpointKey lane laneKey
#print axioms e050

theorem e049 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p049 master masterKey checkpoint checkpointKey lane derivedLane laneKey))
  (NMX_CB04.r049 (NMX_DecoderLibrary.install L) D ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (NMX_Carrier.key derivedLane) (NMX_Carrier.key laneKey)) := by
 unfold NMX_SF04.p049 NMX_CB04.r049
 unfold NMX_SourceProgram.raw
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)
   simp only [decide_not,NMX_KeyCarrier.key_equal]
   exact NMX_HeterogeneousPrimitives.pure id _
 · intro wrongLanePda
   exact NMX_SemanticF04.e050 owners ln rn L D master masterKey checkpoint checkpointKey lane laneKey wrongLanePda
#print axioms e049

theorem e048 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p048 laneAccount master masterKey checkpoint checkpointKey lane derivedLane))
  (NMX_CB04.r048 (NMX_DecoderLibrary.install L) D (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (NMX_Carrier.key derivedLane)) := by
 unfold NMX_SF04.p048 NMX_CB04.r048
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.key laneAccount.key
 · intro laneKey
   exact NMX_SemanticF04.e049 owners ln rn L D master masterKey checkpoint checkpointKey lane derivedLane laneKey
#print axioms e048

theorem e047 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p047 pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds))
  (NMX_CB04.r047 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) ((fun x => x.val.map NMX_Carrier.bytes) laneSeeds)) := by
 unfold NMX_SF04.p047 NMX_CB04.r047
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_CommandTransport.pda owners ln rn laneSeeds pool
 · intro derivedLane
   exact NMX_SemanticF04.e048 owners ln rn L D laneAccount master masterKey checkpoint checkpointKey lane derivedLane
#print axioms e047

theorem e046 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p046 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane))
  (NMX_CB04.r046 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane)) := by
 unfold NMX_SF04.p046 NMX_CB04.r046
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.bytes id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.bytes (Array.to_slice masterKey)
 · intro laneMasterSeed
   let laneIdSeed := Array.to_slice (Array.make 1#usize [outputLane])
   let laneBump := Array.to_slice (Array.make 1#usize [lane.payload.bump])
   let laneSeeds := Array.to_slice (Array.make 4#usize [
     r1_pool_adapter.PAIR_FOREST_LANE_SEED,laneMasterSeed,laneIdSeed,laneBump])
   simpa only [laneSeeds,laneIdSeed,laneBump,NMX_SeedFrames.lane,NMX_SeedFrames.single,NMX_Carrier.lane] using (NMX_SemanticF04.e047 owners ln rn L D pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds)
#print axioms e046

theorem e045 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p045 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane))
  (NMX_CB04.r045 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane)) := by
 unfold NMX_SF04.p045 NMX_CB04.r045
 rw [NMX_DenoteStep.check]
 have same : (lane.payload.lane_id != outputLane) =
   (((fun x : Box Lane => NMX_Carrier.lane x.payload) lane).lane_id != byte outputLane) :=
   NMX_ScalarBne.byte_ne lane.payload.lane_id outputLane
 rw [← same]
 apply NMX_CheckTransport.step
 exact NMX_SemanticF04.e046 owners ln rn L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e045

theorem e044 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p044 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster))
  (NMX_CB04.r044 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (id wrongLaneMaster)) := by
 unfold NMX_SF04.p044 NMX_CB04.r044
 rw [NMX_DenoteStep.check]
 apply NMX_CheckTransport.step
 exact NMX_SemanticF04.e045 owners ln rn L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e044

theorem e043 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p043 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes))
  (NMX_CB04.r043 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (NMX_Carrier.key laneMasterBytes)) := by
 unfold NMX_SF04.p043 NMX_CB04.r043
 unfold NMX_SourceProgram.raw
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)
   rw [NMX_ArrayEqualityCarrier.array_ne]
   exact NMX_HeterogeneousPrimitives.pure id _
 · intro wrongLaneMaster
   exact NMX_SemanticF04.e044 owners ln rn L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster
#print axioms e043

theorem e042 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p042 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane))
  (NMX_CB04.r042 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane)) := by
 unfold NMX_SF04.p042 NMX_CB04.r042
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.key masterKey
 · intro laneMasterBytes
   exact NMX_SemanticF04.e043 owners ln rn L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes
#print axioms e042

theorem e041 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p041 pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes))
  (NMX_CB04.r041 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (NMX_Carrier.key checkpointKey) (NMX_Carrier.bytes laneBytes)) := by
 unfold NMX_SF04.p041 NMX_CB04.r041
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind (fun x => NMX_Carrier.lane x.payload) id
 · exact NMX_CommandTransport.lane owners ln rn lanePacket laneBytes
 · intro lane
   exact NMX_SemanticF04.e042 owners ln rn L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e041
end NMX_SemanticF04
end
