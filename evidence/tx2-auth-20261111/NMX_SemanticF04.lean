import NMX_SF04
import NMX_CB04
import NMX_DenoteStep
import NMX_BoxCommands
import NMX_CommandTransport
import NMX_IndexTransport
import NMX_ScalarBne
import NMX_ArrayEqualityCarrier
import NMX_SemanticF05
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF04
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e050 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p050 master masterKey checkpoint checkpointKey lane laneKey wrongLanePda))
  (NMX_CB04.r050 (NMX_DecoderLibrary.install L) D ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (key laneKey) (id wrongLanePda)) := by
 unfold NMX_SF04.p050 NMX_CB04.r050
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e049 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p049 master masterKey checkpoint checkpointKey lane derivedLane laneKey))
  (NMX_CB04.r049 (NMX_DecoderLibrary.install L) D ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (key derivedLane) (key laneKey)) := by
 unfold NMX_SF04.p049 NMX_CB04.r049
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro wrongLanePda
   exact NMX_SemanticF04.e050 owners ln rn L D lanePacket registryPacket master masterKey checkpoint checkpointKey lane laneKey wrongLanePda
#print axioms e049

theorem e048 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p048 laneAccount master masterKey checkpoint checkpointKey lane derivedLane))
  (NMX_CB04.r048 (NMX_DecoderLibrary.install L) D (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (key derivedLane)) := by
 unfold NMX_SF04.p048 NMX_CB04.r048
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key laneAccount.key
 · intro laneKey
   exact NMX_SemanticF04.e049 owners ln rn L D lanePacket registryPacket master masterKey checkpoint checkpointKey lane derivedLane laneKey
#print axioms e048

theorem e047 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p047 pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds))
  (NMX_CB04.r047 (NMX_DecoderLibrary.install L) D (key pool) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) ((fun x => x.val.map bytes) laneSeeds)) := by
 unfold NMX_SF04.p047 NMX_CB04.r047
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · fail "Unimplemented carrier step"
 · intro derivedLane
   exact NMX_SemanticF04.e048 owners ln rn L D lanePacket registryPacket laneAccount master masterKey checkpoint checkpointKey lane derivedLane
#print axioms e047

theorem e046 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p046 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane))
  (NMX_CB04.r046 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane)) := by
 unfold NMX_SF04.p046 NMX_CB04.r046
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind bytes id
 · exact NMX_HeterogeneousPrimitives.pure bytes (Array.to_slice masterKey)
 · intro laneMasterSeed
   exact NMX_SemanticF04.e047 owners ln rn L D lanePacket registryPacket pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds
#print axioms e046

theorem e045 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p045 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane))
  (NMX_CB04.r045 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane)) := by
 unfold NMX_SF04.p045 NMX_CB04.r045
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e044 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p044 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster))
  (NMX_CB04.r044 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (id wrongLaneMaster)) := by
 unfold NMX_SF04.p044 NMX_CB04.r044
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e043 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p043 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes))
  (NMX_CB04.r043 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane) (key laneMasterBytes)) := by
 unfold NMX_SF04.p043 NMX_CB04.r043
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro wrongLaneMaster
   exact NMX_SemanticF04.e044 owners ln rn L D lanePacket registryPacket pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster
#print axioms e043

theorem e042 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p042 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane))
  (NMX_CB04.r042 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_Carrier.lane x.payload) lane)) := by
 unfold NMX_SF04.p042 NMX_CB04.r042
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key masterKey
 · intro laneMasterBytes
   exact NMX_SemanticF04.e043 owners ln rn L D lanePacket registryPacket pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes
#print axioms e042

theorem e041 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p041 pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes))
  (NMX_CB04.r041 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) (bytes laneBytes)) := by
 unfold NMX_SF04.p041 NMX_CB04.r041
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind (fun x => NMX_Carrier.lane x.payload) id
 · fail "Unimplemented carrier step"
 · intro lane
   exact NMX_SemanticF04.e042 owners ln rn L D lanePacket registryPacket pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e041
end NMX_SemanticF04
end
