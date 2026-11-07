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
import NMX_R2_SemanticF02
set_option autoImplicit false
noncomputable section
namespace NMX_R2_SemanticF01
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_R2_Carrier
attribute [local instance] Classical.propDecidable

theorem e020 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p020 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_R2_CB01.r020 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey)) := by
 unfold NMX_R2_SF01.p020 NMX_R2_CB01.r020
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.byte id
 · exact NMX_R2_HeterogeneousPrimitives.pure byte 255#u8
 · intro allLanes
   exact NMX_R2_SemanticF02.e021 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes
#print axioms e020

theorem e019 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p019 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster))
  (NMX_R2_CB01.r019 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) (id wrongMaster)) := by
 unfold NMX_R2_SF01.p019 NMX_R2_CB01.r019
 rw [NMX_R2_DenoteStep.check]
 apply NMX_R2_CheckTransport.step
 exact NMX_R2_SemanticF01.e020 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e019

theorem e018 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p018 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes))
  (NMX_R2_CB01.r018 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey) (NMX_R2_Carrier.key masterKeyBytes)) := by
 unfold NMX_R2_SF01.p018 NMX_R2_CB01.r018
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · change NMX_R2_Heterogeneous.Refines id (NMX_R2_ResultRelation.raw _) (RSL.RS.pure _)
   rw [NMX_R2_ArrayEqualityCarrier.array_ne]
   exact NMX_R2_HeterogeneousPrimitives.pure id _
 · intro wrongMaster
   exact NMX_R2_SemanticF01.e019 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster
#print axioms e018

theorem e017 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p017 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey))
  (NMX_R2_CB01.r017 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master) (NMX_R2_Carrier.key masterKey)) := by
 unfold NMX_R2_SF01.p017 NMX_R2_CB01.r017
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.key id
 · exact NMX_R2_HeterogeneousPrimitives.pure NMX_R2_Carrier.key masterKey
 · intro masterKeyBytes
   exact NMX_R2_SemanticF01.e018 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes
#print axioms e017

theorem e016 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p016 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master))
  (NMX_R2_CB01.r016 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) ((fun x => NMX_R2_Carrier.master x.payload) master)) := by
 unfold NMX_R2_SF01.p016 NMX_R2_CB01.r016
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.key id
 · exact NMX_R2_HeterogeneousPrimitives.pure NMX_R2_Carrier.key masterAccount.key
 · intro masterKey
   exact NMX_R2_SemanticF01.e017 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e016

theorem e015 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p015 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes))
  (NMX_R2_CB01.r015 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) (NMX_R2_Carrier.bytes masterBytes)) := by
 unfold NMX_R2_SF01.p015 NMX_R2_CB01.r015
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind (fun x => NMX_R2_Carrier.master x.payload) id
 · exact NMX_R2_BoxCommands.master L owners.master masterBytes
 · intro master
   exact NMX_R2_SemanticF01.e016 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master
#print axioms e015

theorem e014 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p014 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount))
  (NMX_R2_CB01.r014 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount)) := by
 unfold NMX_R2_SF01.p014 NMX_R2_CB01.r014
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.bytes id
 · exact NMX_R2_CommandTransport.data owners ln rn masterAccount
 · intro masterBytes
   exact NMX_R2_SemanticF01.e015 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes
#print axioms e014

theorem e013 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p013 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_R2_CB01.r013 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) (NMX_R2_Carrier.account verifierCheckpoint)) := by
 unfold NMX_R2_SF01.p013 NMX_R2_CB01.r013
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · exact NMX_R2_HeterogeneousPrimitives.refl _
 · intro _unit
   exact NMX_R2_SemanticF01.e014 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount
#print axioms e013

theorem e012 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p012 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_R2_CB01.r012 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) (NMX_R2_Carrier.account verifierCheckpoint)) := by
 unfold NMX_R2_SF01.p012 NMX_R2_CB01.r012
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · exact NMX_R2_HeterogeneousPrimitives.refl _
 · intro _unit
   exact NMX_R2_SemanticF01.e013 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e012

theorem e011 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF01.p011 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_R2_CB01.r011 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) (NMX_R2_Carrier.account verifierCheckpoint)) := by
 unfold NMX_R2_SF01.p011 NMX_R2_CB01.r011
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · exact NMX_R2_HeterogeneousPrimitives.refl _
 · intro _unit
   exact NMX_R2_SemanticF01.e012 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e011
end NMX_R2_SemanticF01
end
