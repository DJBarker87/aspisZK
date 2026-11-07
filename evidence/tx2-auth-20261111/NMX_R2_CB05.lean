import NMX_R2_CanonicalTarget
set_option autoImplicit false
namespace NMX_R2_CB05
open RSL

def r055 (L : RSL.PoolLib) (D : RSL.DeployedIds) (master : RSL.Master) (checkpoint : RSL.Checkpoint) (lane : RSL.LaneState) (laneKey : RSL.B32) (live : RSL.LiveSnapshot) (returnedMasterBytes : RSL.B32) (returnedCheckpointBytes : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (laneKey)) (fun returnedLaneBytes =>
  RSL.RS.pure ⟨returnedMasterBytes,returnedCheckpointBytes,returnedLaneBytes,master,checkpoint,lane,live⟩)

def r054 (L : RSL.PoolLib) (D : RSL.DeployedIds) (master : RSL.Master) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (laneKey : RSL.B32) (live : RSL.LiveSnapshot) (returnedMasterBytes : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (checkpointKey)) (fun returnedCheckpointBytes =>
  NMX_R2_CB05.r055 L D master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes)

def r053 (L : RSL.PoolLib) (D : RSL.DeployedIds) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (laneKey : RSL.B32) (live : RSL.LiveSnapshot) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (masterKey)) (fun returnedMasterBytes =>
  NMX_R2_CB05.r054 L D master checkpoint checkpointKey lane laneKey live returnedMasterBytes)

def r052 (L : RSL.PoolLib) (D : RSL.DeployedIds) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (laneKey : RSL.B32) (snapshotPool : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.bind (RSL.RS.lift RSL.Spec.alloc) (fun _ => RSL.RS.pure (⟨snapshotPool,master.identity.deployment_domain,
  lane.tree.next_leaf_index,lane.tree.next_leaf_index,
  lane.tree.root,lane.tree.frontier⟩ : RSL.LiveSnapshot))) (fun live =>
  NMX_R2_CB05.r053 L D master masterKey checkpoint checkpointKey lane laneKey live)

def r051 (L : RSL.PoolLib) (D : RSL.DeployedIds) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (laneKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (masterKey)) (fun snapshotPool =>
  NMX_R2_CB05.r052 L D master masterKey checkpoint checkpointKey lane laneKey snapshotPool)
end NMX_R2_CB05
