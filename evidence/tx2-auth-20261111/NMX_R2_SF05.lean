import NMX_R2_Skeleton
set_option autoImplicit false
noncomputable section
namespace NMX_R2_SF05
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceProgram
attribute [local instance] Classical.propDecidable

def p055 (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes laneKey)) (fun returnedLaneBytes =>
  .ret ⟨returnedMasterBytes,returnedCheckpointBytes,returnedLaneBytes,master,checkpoint,lane,live⟩)

def p054 (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes checkpointKey)) (fun returnedCheckpointBytes =>
  NMX_R2_SF05.p055 master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes)

def p053 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun returnedMasterBytes =>
  NMX_R2_SF05.p054 master checkpoint checkpointKey lane laneKey live returnedMasterBytes)

def p052 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.snapshot ⟨snapshotPool,master.payload.identity.deployment_domain,
  lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
  lane.payload.tree.root,lane.payload.tree.frontier⟩)) (fun live =>
  NMX_R2_SF05.p053 master masterKey checkpoint checkpointKey lane laneKey live)

def p051 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun snapshotPool =>
  NMX_R2_SF05.p052 master masterKey checkpoint checkpointKey lane laneKey snapshotPool)
end NMX_R2_SF05
end
