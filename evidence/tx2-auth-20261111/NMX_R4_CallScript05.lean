import NMX_R4_CallProgram
import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallScript05
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram

def t055 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) : Program (core.result.Result Auth PE) := do
  let returnedLaneBytes ← scalar (ops.op39
      laneKey)
  Program.ret (core.result.Result.Ok
    {
      masterAccount := returnedMasterBytes,
      checkpointAccount :=
        returnedCheckpointBytes,
      selectedLaneAccount :=
        returnedLaneBytes,
      master := master,
      checkpoint := checkpoint,
      selectedLane := lane,
      liveSnapshot := live
    })

def t054 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) : Program (core.result.Result Auth PE) := do
  let returnedCheckpointBytes ← scalar (ops.op39
      checkpointKey)
  NMX_R4_CallScript05.t055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes

def t053 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) : Program (core.result.Result Auth PE) := do
  let returnedMasterBytes ← scalar (ops.op39
      masterKey)
  NMX_R4_CallScript05.t054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes

def t052 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) : Program (core.result.Result Auth PE) := do
  let live ← snapshot {
  pool := snapshotPool,
  deployment_domain :=
  master.payload.identity.deployment_domain,
  sequence :=
  lane.payload.tree.next_leaf_index,
  next_pair_index :=
  lane.payload.tree.next_leaf_index,
  current_root :=
  lane.payload.tree.root,
  frontier :=
  lane.payload.tree.frontier
  }
  NMX_R4_CallScript05.t053 owners ops master masterKey checkpoint checkpointKey lane laneKey live


def t051 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let snapshotPool ← scalar (ops.op39
      masterKey)
  NMX_R4_CallScript05.t052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool
end NMX_R4_CallScript05
end
