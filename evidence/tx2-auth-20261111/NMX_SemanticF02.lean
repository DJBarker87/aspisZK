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
import NMX_SemanticF03a
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF02
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e030 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p030 pool outputLane checkpointAccount laneAccount master masterKey checkpoint))
  (NMX_CB02.r030 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint)) := by
 unfold NMX_SF02.p030 NMX_CB02.r030
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.key masterKey
 · intro checkpointMasterBytes
   exact NMX_SemanticF03a.e031 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes
#print axioms e030

theorem e029 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p029 pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes))
  (NMX_CB02.r029 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) (NMX_Carrier.bytes checkpointBytes)) := by
 unfold NMX_SF02.p029 NMX_CB02.r029
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind (fun x => NMX_Carrier.checkpoint x.payload) id
 · exact NMX_BoxCommands.checkpoint L owners.checkpoint checkpointBytes
 · intro checkpoint
   exact NMX_SemanticF02.e030 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e029

theorem e028 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p028 pool outputLane checkpointAccount laneAccount master masterKey))
  (NMX_CB02.r028 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey)) := by
 unfold NMX_SF02.p028 NMX_CB02.r028
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.bytes id
 · exact NMX_CommandTransport.data owners ln rn checkpointAccount
 · intro checkpointBytes
   exact NMX_SemanticF02.e029 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes
#print axioms e028

theorem e027 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p027 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_CB02.r027 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key verifier) (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.long slot) (NMX_Carrier.account masterAccount) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) (NMX_Carrier.account registryAccount) (NMX_Carrier.account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey)) := by
 unfold NMX_SF02.p027 NMX_CB02.r027
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · change NMX_Heterogeneous.Refines id _
     (NMX_RegistryTransport.model (NMX_DecoderLibrary.install L) D
       ⟨verifier,pool,masterAccount,master.payload,registryAccount,entryAccount,slot⟩)
   exact NMX_RegistryTransport.packet rn (NMX_DecoderLibrary.install L) D registryPacket _
 · intro _unit
   exact NMX_SemanticF02.e028 owners ln rn L D lanePacket pool outputLane checkpointAccount laneAccount master masterKey
#print axioms e027

theorem e026 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p026 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda))
  (NMX_CB02.r026 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key verifier) (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.long slot) (NMX_Carrier.account masterAccount) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) (NMX_Carrier.account registryAccount) (NMX_Carrier.account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) (id wrongMasterPda)) := by
 unfold NMX_SF02.p026 NMX_CB02.r026
 rw [NMX_DenoteStep.check]
 apply NMX_CheckTransport.step
 exact NMX_SemanticF02.e027 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e026

theorem e025 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p025 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster))
  (NMX_CB02.r025 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key verifier) (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.long slot) (NMX_Carrier.account masterAccount) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) (NMX_Carrier.account registryAccount) (NMX_Carrier.account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) (NMX_Carrier.key derivedMaster)) := by
 unfold NMX_SF02.p025 NMX_CB02.r025
 unfold NMX_SourceProgram.raw
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)
   simp only [decide_not,NMX_KeyCarrier.key_equal]
   exact NMX_HeterogeneousPrimitives.pure id _
 · intro wrongMasterPda
   exact NMX_SemanticF02.e026 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda
#print axioms e025

theorem e024 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p024 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds))
  (NMX_CB02.r024 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key verifier) (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.long slot) (NMX_Carrier.account masterAccount) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) (NMX_Carrier.account registryAccount) (NMX_Carrier.account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) ((fun x => x.val.map NMX_Carrier.bytes) masterSeeds)) := by
 unfold NMX_SF02.p024 NMX_CB02.r024
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_CommandTransport.pda owners ln rn masterSeeds pool
 · intro derivedMaster
   exact NMX_SemanticF02.e025 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster
#print axioms e024

theorem e023 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p023 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey))
  (NMX_CB02.r023 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key verifier) (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.long slot) (NMX_Carrier.account masterAccount) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) (NMX_Carrier.account registryAccount) (NMX_Carrier.account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) (NMX_Carrier.key mintKey)) := by
 unfold NMX_SF02.p023 NMX_CB02.r023
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.bytes id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.bytes (Array.to_slice mintKey)
 · intro mintSeed
   let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
   let masterSeeds := Array.to_slice (Array.make 3#usize [
     r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
   simpa only [masterSeeds,bumpSeed,NMX_SeedFrames.master,NMX_SeedFrames.single,NMX_Carrier.master] using (NMX_SemanticF02.e024 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds)
#print axioms e023

theorem e022 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p022 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_CB02.r022 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key verifier) (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.long slot) (NMX_Carrier.account masterAccount) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) (NMX_Carrier.account registryAccount) (NMX_Carrier.account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey)) := by
 unfold NMX_SF02.p022 NMX_CB02.r022
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind NMX_Carrier.key id
 · exact NMX_HeterogeneousPrimitives.pure NMX_Carrier.key master.payload.identity.asset_mint
 · intro mintKey
   exact NMX_SemanticF02.e023 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey
#print axioms e022

theorem e021 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p021 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes))
  (NMX_CB02.r021 (NMX_DecoderLibrary.install L) D (NMX_Carrier.key verifier) (NMX_Carrier.key pool) (NMX_Carrier.byte outputLane) (NMX_Carrier.long slot) (NMX_Carrier.account masterAccount) (NMX_Carrier.account checkpointAccount) (NMX_Carrier.account laneAccount) (NMX_Carrier.account registryAccount) (NMX_Carrier.account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (NMX_Carrier.key masterKey) (NMX_Carrier.byte allLanes)) := by
 unfold NMX_SF02.p021 NMX_CB02.r021
 rw [NMX_DenoteStep.check]
 have same : (master.payload.initialized_lane_mask != allLanes) =
  (((fun x : Box Master => NMX_Carrier.master x.payload) master).initialized_lane_mask != byte allLanes) :=
  NMX_ScalarBne.byte_ne master.payload.initialized_lane_mask allLanes
 rw [← same]
 apply NMX_CheckTransport.step
 exact NMX_SemanticF02.e022 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e021
end NMX_SemanticF02
end
