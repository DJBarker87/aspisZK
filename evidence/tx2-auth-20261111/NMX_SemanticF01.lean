import NMX_SF01
import NMX_CB01
import NMX_DenoteStep
import NMX_BoxCommands
import NMX_CommandTransport
import NMX_IndexTransport
import NMX_ScalarBne
import NMX_ArrayEqualityCarrier
import NMX_SemanticF02
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF01
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable

theorem e020 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p020 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_CB01.r020 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey)) := by
 unfold NMX_SF01.p020 NMX_CB01.r020
 apply NMX_Heterogeneous.bind byte id
 · exact NMX_HeterogeneousPrimitives.pure byte 255#u8
 · intro allLanes
   exact NMX_SemanticF02.e021 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes
#print axioms e020

theorem e019 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p019 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster))
  (NMX_CB01.r019 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) (id wrongMaster)) := by
 unfold NMX_SF01.p019 NMX_CB01.r019
 rw [NMX_DenoteStep.check]
 fail "Unimplemented carrier step"

theorem e018 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p018 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes))
  (NMX_CB01.r018 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey) (key masterKeyBytes)) := by
 unfold NMX_SF01.p018 NMX_CB01.r018
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro wrongMaster
   exact NMX_SemanticF01.e019 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster
#print axioms e018

theorem e017 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p017 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_CB01.r017 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master) (key masterKey)) := by
 unfold NMX_SF01.p017 NMX_CB01.r017
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key masterKey
 · intro masterKeyBytes
   exact NMX_SemanticF01.e018 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes
#print axioms e017

theorem e016 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p016 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master))
  (NMX_CB01.r016 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) ((fun x => NMX_Carrier.master x.payload) master)) := by
 unfold NMX_SF01.p016 NMX_CB01.r016
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key masterAccount.key
 · intro masterKey
   exact NMX_SemanticF01.e017 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e016

theorem e015 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p015 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes))
  (NMX_CB01.r015 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) (bytes masterBytes)) := by
 unfold NMX_SF01.p015 NMX_CB01.r015
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind (fun x => NMX_Carrier.master x.payload) id
 · exact NMX_BoxCommands.master L owners.master masterBytes
 · intro master
   exact NMX_SemanticF01.e016 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master
#print axioms e015

theorem e014 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p014 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount))
  (NMX_CB01.r014 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount)) := by
 unfold NMX_SF01.p014 NMX_CB01.r014
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind bytes id
 · fail "Unimplemented carrier step"
 · intro masterBytes
   exact NMX_SemanticF01.e015 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes
#print axioms e014

theorem e013 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p013 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_CB01.r013 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account proof) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) (account verifierCheckpoint)) := by
 unfold NMX_SF01.p013 NMX_CB01.r013
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro _unit
   exact NMX_SemanticF01.e014 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount
#print axioms e013

theorem e012 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p012 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_CB01.r012 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account proof) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) (account verifierCheckpoint)) := by
 unfold NMX_SF01.p012 NMX_CB01.r012
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro _unit
   exact NMX_SemanticF01.e013 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e012

theorem e011 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF01.p011 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_CB01.r011 (NMX_DecoderLibrary.install L) D (key verifier) (key pool) (byte outputLane) (long slot) (account proof) (account masterAccount) (account checkpointAccount) (account laneAccount) (account registryAccount) (account entryAccount) (account verifierCheckpoint)) := by
 unfold NMX_SF01.p011 NMX_CB01.r011
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind id id
 · fail "Unimplemented carrier step"
 · intro _unit
   exact NMX_SemanticF01.e012 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e011
end NMX_SemanticF01
end
