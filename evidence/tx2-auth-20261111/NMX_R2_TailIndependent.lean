import NMX_R2_SF05
import NMX_R2_CB05
import NMX_R2_DenoteStep
import NMX_R2_BoxCommands
import NMX_R2_IndexTransport
import NMX_R2_ScalarBne
import NMX_R2_ArrayEqualityCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_R2_TailIndependent
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_R2_Carrier
attribute [local instance] Classical.propDecidable

theorem e055 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF05.p055 master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes))
  (NMX_R2_CB05.r055 (NMX_R2_DecoderLibrary.install L) D ((fun x => NMX_R2_Carrier.master x.payload) master) ((fun x => NMX_R2_Carrier.checkpoint x.payload) checkpoint) ((fun x => NMX_R2_Carrier.lane x.payload) lane) (key laneKey) ((fun x => NMX_R2_Carrier.snapshot x.payload) live) (key returnedMasterBytes) (key returnedCheckpointBytes)) := by
 unfold NMX_R2_SF05.p055 NMX_R2_CB05.r055
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind key id
 · exact NMX_R2_HeterogeneousPrimitives.pure key laneKey
 · intro returnedLaneBytes
   exact NMX_R2_HeterogeneousPrimitives.pure id _
#print axioms e055

theorem e054 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF05.p054 master checkpoint checkpointKey lane laneKey live returnedMasterBytes))
  (NMX_R2_CB05.r054 (NMX_R2_DecoderLibrary.install L) D ((fun x => NMX_R2_Carrier.master x.payload) master) ((fun x => NMX_R2_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_R2_Carrier.lane x.payload) lane) (key laneKey) ((fun x => NMX_R2_Carrier.snapshot x.payload) live) (key returnedMasterBytes)) := by
 unfold NMX_R2_SF05.p054 NMX_R2_CB05.r054
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind key id
 · exact NMX_R2_HeterogeneousPrimitives.pure key checkpointKey
 · intro returnedCheckpointBytes
   exact NMX_R2_TailIndependent.e055 owners ln rn L D master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes
#print axioms e054

theorem e053 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF05.p053 master masterKey checkpoint checkpointKey lane laneKey live))
  (NMX_R2_CB05.r053 (NMX_R2_DecoderLibrary.install L) D ((fun x => NMX_R2_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_R2_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_R2_Carrier.lane x.payload) lane) (key laneKey) ((fun x => NMX_R2_Carrier.snapshot x.payload) live)) := by
 unfold NMX_R2_SF05.p053 NMX_R2_CB05.r053
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind key id
 · exact NMX_R2_HeterogeneousPrimitives.pure key masterKey
 · intro returnedMasterBytes
   exact NMX_R2_TailIndependent.e054 owners ln rn L D master checkpoint checkpointKey lane laneKey live returnedMasterBytes
#print axioms e053

theorem e052 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF05.p052 master masterKey checkpoint checkpointKey lane laneKey snapshotPool))
  (NMX_R2_CB05.r052 (NMX_R2_DecoderLibrary.install L) D ((fun x => NMX_R2_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_R2_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_R2_Carrier.lane x.payload) lane) (key laneKey) (key snapshotPool)) := by
 unfold NMX_R2_SF05.p052 NMX_R2_CB05.r052
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind (fun x => NMX_R2_Carrier.snapshot x.payload) id
 · exact NMX_R2_HeterogeneousPrimitives.allocation (fun x => NMX_R2_Carrier.snapshot x.payload) (⟨owners.snapshot,⟨snapshotPool,master.payload.identity.deployment_domain,
  lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
  lane.payload.tree.root,lane.payload.tree.frontier⟩⟩ : Box Snapshot)
 · intro live
   exact NMX_R2_TailIndependent.e053 owners ln rn L D master masterKey checkpoint checkpointKey lane laneKey live
#print axioms e052

theorem e051 (owners : Owners) (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines id
  (NMX_R2_Semantics.denote owners ln rn (NMX_R2_SF05.p051 master masterKey checkpoint checkpointKey lane laneKey))
  (NMX_R2_CB05.r051 (NMX_R2_DecoderLibrary.install L) D ((fun x => NMX_R2_Carrier.master x.payload) master) (key masterKey) ((fun x => NMX_R2_Carrier.checkpoint x.payload) checkpoint) (key checkpointKey) ((fun x => NMX_R2_Carrier.lane x.payload) lane) (key laneKey)) := by
 unfold NMX_R2_SF05.p051 NMX_R2_CB05.r051
 rw [NMX_R2_DenoteStep.call]
 apply NMX_R2_Heterogeneous.bind key id
 · exact NMX_R2_HeterogeneousPrimitives.pure key masterKey
 · intro snapshotPool
   exact NMX_R2_TailIndependent.e052 owners ln rn L D master masterKey checkpoint checkpointKey lane laneKey snapshotPool
#print axioms e051
end NMX_R2_TailIndependent
end
