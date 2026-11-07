import NMX_SF02
import NMX_CB02
import NMX_DenoteStep
import NMX_BoxCommands
import NMX_CommandTransport
import NMX_IndexTransport
import NMX_ScalarBne
import NMX_ArrayEqualityCarrier
import NMX_SemanticF03
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF02
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e030 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p030 pool outputLane checkpointAccount laneAccount master masterKey checkpoint))
  (NMX_CB02.r030 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_Carrier.checkpoint x.payload) checkpoint)) := by
 unfold NMX_SF02.p030 NMX_CB02.r030
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key masterKey
 · intro checkpointMasterBytes
   exact NMX_SemanticF03.e031 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes
#print axioms e030

theorem e029 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p029 pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes))
  (NMX_CB02.r029 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) (bytes checkpointBytes)) := by
 unfold NMX_SF02.p029 NMX_CB02.r029
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind (fun x => NMX_Carrier.checkpoint x.payload) id
 · exact NMX_BoxCommands.checkpoint L owners.checkpoint checkpointBytes
 · intro checkpoint
   exact NMX_SemanticF02.e030 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e029

theorem e028 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p028 pool outputLane checkpointAccount laneAccount master masterKey))
  (NMX_CB02.r028 (NMX_DecoderLibrary.install L) D (key pool) (byte outputLane) (account checkpointAccount) (account laneAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey)) := by
 unfold NMX_SF02.p028 NMX_CB02.r028
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind bytes id
 · fail "Unimplemented carrier step"
 · intro checkpointBytes
   exact NMX_SemanticF02.e029 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes
#print axioms e028

theorem e027 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p027 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_CB02.r027 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey)) := by
 unfold NMX_SF02.p027 NMX_CB02.r027
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro _unit
   exact NMX_SemanticF02.e028 owners ln rn L D lanePacket registryPacket pool outputLane checkpointAccount laneAccount master masterKey
#print axioms e027

theorem e026 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p026 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda))
  (NMX_CB02.r026 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) (id wrongMasterPda)) := by
 unfold NMX_SF02.p026 NMX_CB02.r026
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e025 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p025 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster))
  (NMX_CB02.r025 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) (key derivedMaster)) := by
 unfold NMX_SF02.p025 NMX_CB02.r025
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro wrongMasterPda
   exact NMX_SemanticF02.e026 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda
#print axioms e025

theorem e024 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p024 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds))
  (NMX_CB02.r024 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) ((fun x => x.val.map bytes) masterSeeds)) := by
 unfold NMX_SF02.p024 NMX_CB02.r024
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · fail "Unimplemented carrier step"
 · intro derivedMaster
   exact NMX_SemanticF02.e025 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster
#print axioms e024

theorem e023 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p023 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey))
  (NMX_CB02.r023 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) (key mintKey)) := by
 unfold NMX_SF02.p023 NMX_CB02.r023
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind bytes id
 · exact NMX_HeterogeneousPrimitives.pure bytes (Array.to_slice mintKey)
 · intro mintSeed
   exact NMX_SemanticF02.e024 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds
#print axioms e023

theorem e022 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p022 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_CB02.r022 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey)) := by
 unfold NMX_SF02.p022 NMX_CB02.r022
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key 255#u8
 · intro mintKey
   exact NMX_SemanticF02.e023 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey
#print axioms e022

theorem e021 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF02.p021 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes))
  (NMX_CB02.r021 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) (byte allLanes)) := by
 unfold NMX_SF02.p021 NMX_CB02.r021
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"
end NMX_SemanticF02
end
