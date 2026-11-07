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
import NMX_R2_SemanticF01
set_option autoImplicit false
noncomputable section
namespace NMX_R2_SemanticF00
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_R2_Carrier
attribute [local instance] Classical.propDecidable

theorem e010 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p010 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_R2_CB00.r010 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) (NMX_R2_Carrier.account verifierCheckpoint)) := by
 unfold NMX_R2_SF00.p010 NMX_R2_CB00.r010
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · exact NMX_R2_HeterogeneousPrimitives.refl _
 · intro _unit
   exact NMX_R2_SemanticF01.e011 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e010

theorem e009 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p009 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_R2_CB00.r009 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) (NMX_R2_Carrier.account verifierCheckpoint)) := by
 unfold NMX_R2_SF00.p009 NMX_R2_CB00.r009
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · exact NMX_R2_HeterogeneousPrimitives.refl _
 · intro _unit
   exact NMX_R2_SemanticF00.e010 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e009

theorem e008 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p008 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))
  (NMX_R2_CB00.r008 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount) (NMX_R2_Carrier.account verifierCheckpoint)) := by
 unfold NMX_R2_SF00.p008 NMX_R2_CB00.r008
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind id id
 · exact NMX_R2_HeterogeneousPrimitives.refl _
 · intro _unit
   exact NMX_R2_SemanticF00.e009 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e008

theorem e007 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (count : accounts.val.length = 7) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p007 verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount))
  (NMX_R2_CB00.r007 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) ((fun x => x.val.map NMX_R2_Carrier.account) accounts) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount) (NMX_R2_Carrier.account entryAccount)) := by
 unfold NMX_R2_SF00.p007 NMX_R2_CB00.r007
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.account id
 · exact NMX_R2_IndexTransport.inside NMX_R2_Carrier.account accounts 6#usize (by rw [count]; decide)
 · intro verifierCheckpoint
   exact NMX_R2_SemanticF00.e008 owners ln rn L D lanePacket registryPacket verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e007

theorem e006 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (count : accounts.val.length = 7) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p006 verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount))
  (NMX_R2_CB00.r006 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) ((fun x => x.val.map NMX_R2_Carrier.account) accounts) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount) (NMX_R2_Carrier.account registryAccount)) := by
 unfold NMX_R2_SF00.p006 NMX_R2_CB00.r006
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.account id
 · exact NMX_R2_IndexTransport.inside NMX_R2_Carrier.account accounts 5#usize (by rw [count]; decide)
 · intro entryAccount
   exact NMX_R2_SemanticF00.e007 owners ln rn L D lanePacket registryPacket verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount count
#print axioms e006

theorem e005 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (count : accounts.val.length = 7) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p005 verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount))
  (NMX_R2_CB00.r005 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) ((fun x => x.val.map NMX_R2_Carrier.account) accounts) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount) (NMX_R2_Carrier.account laneAccount)) := by
 unfold NMX_R2_SF00.p005 NMX_R2_CB00.r005
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.account id
 · exact NMX_R2_IndexTransport.inside NMX_R2_Carrier.account accounts 4#usize (by rw [count]; decide)
 · intro registryAccount
   exact NMX_R2_SemanticF00.e006 owners ln rn L D lanePacket registryPacket verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount count
#print axioms e005

theorem e004 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (count : accounts.val.length = 7) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p004 verifier accounts pool outputLane slot proof masterAccount checkpointAccount))
  (NMX_R2_CB00.r004 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) ((fun x => x.val.map NMX_R2_Carrier.account) accounts) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount) (NMX_R2_Carrier.account checkpointAccount)) := by
 unfold NMX_R2_SF00.p004 NMX_R2_CB00.r004
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.account id
 · exact NMX_R2_IndexTransport.inside NMX_R2_Carrier.account accounts 3#usize (by rw [count]; decide)
 · intro laneAccount
   exact NMX_R2_SemanticF00.e005 owners ln rn L D lanePacket registryPacket verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount count
#print axioms e004

theorem e003 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (count : accounts.val.length = 7) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p003 verifier accounts pool outputLane slot proof masterAccount))
  (NMX_R2_CB00.r003 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) ((fun x => x.val.map NMX_R2_Carrier.account) accounts) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof) (NMX_R2_Carrier.account masterAccount)) := by
 unfold NMX_R2_SF00.p003 NMX_R2_CB00.r003
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.account id
 · exact NMX_R2_IndexTransport.inside NMX_R2_Carrier.account accounts 2#usize (by rw [count]; decide)
 · intro checkpointAccount
   exact NMX_R2_SemanticF00.e004 owners ln rn L D lanePacket registryPacket verifier accounts pool outputLane slot proof masterAccount checkpointAccount count
#print axioms e003

theorem e002 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (count : accounts.val.length = 7) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p002 verifier accounts pool outputLane slot proof))
  (NMX_R2_CB00.r002 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) ((fun x => x.val.map NMX_R2_Carrier.account) accounts) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot) (NMX_R2_Carrier.account proof)) := by
 unfold NMX_R2_SF00.p002 NMX_R2_CB00.r002
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.account id
 · exact NMX_R2_IndexTransport.inside NMX_R2_Carrier.account accounts 1#usize (by rw [count]; decide)
 · intro masterAccount
   exact NMX_R2_SemanticF00.e003 owners ln rn L D lanePacket registryPacket verifier accounts pool outputLane slot proof masterAccount count
#print axioms e002

theorem e001 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds) (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (count : accounts.val.length = 7) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF00.p001 verifier accounts pool outputLane slot))
  (NMX_R2_CB00.r001 (NMX_R2_DecoderLibrary.install L) D (NMX_R2_Carrier.key verifier) ((fun x => x.val.map NMX_R2_Carrier.account) accounts) (NMX_R2_Carrier.key pool) (NMX_R2_Carrier.byte outputLane) (NMX_R2_Carrier.long slot)) := by
 unfold NMX_R2_SF00.p001 NMX_R2_CB00.r001
 unfold NMX_SourceProgram.raw
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind NMX_R2_Carrier.account id
 · exact NMX_R2_IndexTransport.inside NMX_R2_Carrier.account accounts 0#usize (by rw [count]; decide)
 · intro proof
   exact NMX_R2_SemanticF00.e002 owners ln rn L D lanePacket registryPacket verifier accounts pool outputLane slot proof count
#print axioms e001
end NMX_R2_SemanticF00
end
