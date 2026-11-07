import NMX_R2_SF00
import NMX_R2_CB00
import NMX_R2_DenoteStep
import NMX_R2_CommandTransport
import NMX_R2_RegistryTransport
import NMX_R2_CheckTransport
import NMX_R2_SeedFrames
import NMX_R2_ScalarBne
import NMX_R2_ArrayEqualityCarrier
import NMX_R2_IndexTransport
import NMX_R2_SemanticF03a
set_option autoImplicit false
noncomputable section
namespace NMX_R2_SemanticF02
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_R2_Carrier
attribute [local instance] Classical.propDecidable

theorem e030 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p030 pool outputLane checkpointAccount laneAccount master masterKey checkpoint))
  (NMX_R2_CB02.r030 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) ((fun x => NMX_R2_Carrier.checkpoint x.payload) checkpoint)) := by
 unfold NMX_R2_SF02.p030 NMX_R2_CB02.r030
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.key id
 · exact NMX_R2_HeterogeneousPrimitives.pure NMX_R2_Carrier.key masterKey
 · intro checkpointMasterBytes
   exact NMX_R2_SemanticF03a.e031 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes
#print axioms e030

theorem e029 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p029 pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes))
  (NMX_R2_CB02.r029 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) (NMX_R2_Carrier.bytes checkpointBytes)) := by
 unfold NMX_R2_SF02.p029 NMX_R2_CB02.r029
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind (fun x => NMX_R2_Carrier.checkpoint x.payload) id
 · exact NMX_R2_BoxCommands.checkpoint L owners.checkpoint checkpointBytes
 · intro checkpoint
   exact NMX_R2_SemanticF02.e030 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e029

theorem e028 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p028 pool outputLane checkpointAccount laneAccount master masterKey))
  (NMX_R2_CB02.r028 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey)) := by
 unfold NMX_R2_SF02.p028 NMX_R2_CB02.r028
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.bytes id
 · exact NMX_R2_CommandTransport.data owners ln rn checkpointAccount
 · intro checkpointBytes
   exact NMX_R2_SemanticF02.e029 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes
#print axioms e028

theorem e027 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p027 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_R2_CB02.r027 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey)) := by
 unfold NMX_R2_SF02.p027 NMX_R2_CB02.r027
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · change NMX_R2_Heterogeneous.Refines id _
     (NMX_R2_RegistryTransport.model (NMX_R2_DecoderLibrary.install L) D
       ⟨verifier,pool,masterAccount,master.payload,registryAccount,entryAccount,slot⟩)
   exact NMX_R2_RegistryTransport.packet rn (NMX_R2_DecoderLibrary.install L) D registryPacket _
 · intro _unit
   exact NMX_R2_SemanticF02.e028 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey
#print axioms e027

theorem e026 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p026 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda))
  (NMX_R2_CB02.r026 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) (id wrongMasterPda)) := by
 unfold NMX_R2_SF02.p026 NMX_R2_CB02.r026
 rw [NMX_R2_DenoteStep.check]
 apply NMX_R2_CheckTransport.step
 exact NMX_R2_SemanticF02.e027 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e026

theorem e025 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p025 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster))
  (NMX_R2_CB02.r025 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) (NMX_R2_Carrier.key derivedMaster)) := by
 unfold NMX_R2_SF02.p025 NMX_R2_CB02.r025
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · change NMX_R2_Heterogeneous.Refines id (NMX_R2_ResultRelation.raw _) (RSL.RS.pure _)
   simp only [decide_not,NMX_R2_KeyCarrier.key_equal]
   exact NMX_R2_HeterogeneousPrimitives.pure id _
 · intro wrongMasterPda
   exact NMX_R2_SemanticF02.e026 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda
#print axioms e025

theorem e024 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p024 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds))
  (NMX_R2_CB02.r024 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) ((fun x => x.val.map NMX_R2_Carrier.bytes) masterSeeds)) := by
 unfold NMX_R2_SF02.p024 NMX_R2_CB02.r024
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.key id
 · exact NMX_R2_CommandTransport.pda owners ln rn masterSeeds pool
 · intro derivedMaster
   exact NMX_R2_SemanticF02.e025 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster
#print axioms e024

theorem e023 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p023 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey))
  (NMX_R2_CB02.r023 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) (NMX_R2_Carrier.key mintKey)) := by
 unfold NMX_R2_SF02.p023 NMX_R2_CB02.r023
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.bytes id
 · exact NMX_R2_HeterogeneousPrimitives.pure NMX_R2_Carrier.bytes (Array.to_slice mintKey)
 · intro mintSeed
   let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
   let masterSeeds := Array.to_slice (Array.make 3#usize [
     r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
   simpa only [masterSeeds,bumpSeed,NMX_R2_SeedFrames.master,NMX_R2_SeedFrames.single,NMX_R2_Carrier.master] using (NMX_R2_SemanticF02.e024 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds)
#print axioms e023

theorem e022 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p022 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_R2_CB02.r022 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey)) := by
 unfold NMX_R2_SF02.p022 NMX_R2_CB02.r022
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.key id
 · exact NMX_R2_HeterogeneousPrimitives.pure NMX_R2_Carrier.key master.payload.identity.asset_mint
 · intro mintKey
   exact NMX_R2_SemanticF02.e023 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey
#print axioms e022

theorem e021 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF02.p021 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes))
  (NMX_R2_CB02.r021 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) (NMX_R2_Carrier.byte allLanes)) := by
 unfold NMX_R2_SF02.p021 NMX_R2_CB02.r021
 rw [NMX_R2_DenoteStep.check]
 have same : (master.payload.initialized_lane_mask != allLanes) =
  (((fun x : Box Master => NMX_R2_Carrier.master x.payload) master).initialized_lane_mask != byte allLanes) :=
  NMX_R2_ScalarBne.byte_ne master.payload.initialized_lane_mask allLanes
 rw [← same]
 apply NMX_R2_CheckTransport.step
 exact NMX_R2_SemanticF02.e022 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e021
end NMX_R2_SemanticF02
end
