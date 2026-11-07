import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_Actual05
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

def t055 (owners : Owners) (ops : Ops) (master : Master) (checkpoint : Checkpoint) (lane : Lane) (laneKey : solana_pubkey.Pubkey) (live : Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) : Final := do
  let returnedLaneBytes ←
    ops.op39
      laneKey
  ok (core.result.Result.Ok
    {
      master_account := returnedMasterBytes,
      checkpoint_account :=
        returnedCheckpointBytes,
      selected_lane_account :=
        returnedLaneBytes,
      master := master,
      checkpoint := checkpoint,
      selected_lane := lane,
      live_snapshot := live
    })

def t054 (owners : Owners) (ops : Ops) (master : Master) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (laneKey : solana_pubkey.Pubkey) (live : Snapshot) (returnedMasterBytes : Array U8 32#usize) : Final := do
  let returnedCheckpointBytes ←
    ops.op39
      checkpointKey
  NMX_Actual05.t055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes

def t053 (owners : Owners) (ops : Ops) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (laneKey : solana_pubkey.Pubkey) (live : Snapshot) : Final := do
  let returnedMasterBytes ←
    ops.op39
      masterKey
  NMX_Actual05.t054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes

def t052 (owners : Owners) (ops : Ops) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) : Final := do
  let live : Snapshot := {
  pool := snapshotPool,
  deployment_domain :=
  master.identity.deployment_domain,
  sequence :=
  lane.tree.next_leaf_index,
  next_pair_index :=
  lane.tree.next_leaf_index,
  current_root :=
  lane.tree.root,
  frontier :=
  lane.tree.frontier
  }
  NMX_Actual05.t053 owners ops master masterKey checkpoint checkpointKey lane laneKey live

def t051 (owners : Owners) (ops : Ops) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (laneKey : solana_pubkey.Pubkey) : Final := do
  let snapshotPool ←
    ops.op39
      masterKey
  NMX_Actual05.t052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool
end NMX_Actual05
end
