import NMX_S051
import NMX_S052
import NMX_S053
import NMX_S054
import NMX_S055
set_option autoImplicit false
noncomputable section
namespace NMX_Fold05
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps

def p055 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes laneKey)) (fun returnedLaneBytes =>
  .ret ⟨returnedMasterBytes,returnedCheckpointBytes,returnedLaneBytes,master,checkpoint,lane,live⟩)
def v055 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) : Final :=
  (ops.op39 laneKey) >>= fun value => (fun returnedLaneBytes =>
  ok (.Ok ((⟨returnedMasterBytes,returnedCheckpointBytes,returnedLaneBytes,master,checkpoint,lane,live⟩ : Auth).erase))) value
theorem e055 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) :
 NMX_ValueLink.erase (eval (source ops owners) (p055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes) ()) =
 v055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes := by
 unfold p055 v055
 rw [NMX_S055.step]
 rfl
#print axioms e055

def p054 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes checkpointKey)) (fun returnedCheckpointBytes =>
  NMX_Fold05.p055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes)
def v054 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) : Final :=
  (ops.op39 checkpointKey) >>= fun value => (fun returnedCheckpointBytes =>
  NMX_Fold05.v055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes) value
theorem e054 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) :
 NMX_ValueLink.erase (eval (source ops owners) (p054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes) ()) =
 v054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes := by
 unfold p054 v054
 rw [NMX_S054.step]
 simp only [NMX_Fold05.e055]
#print axioms e054

def p053 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun returnedMasterBytes =>
  NMX_Fold05.p054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes)
def v053 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) : Final :=
  (ops.op39 masterKey) >>= fun value => (fun returnedMasterBytes =>
  NMX_Fold05.v054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes) value
theorem e053 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) :
 NMX_ValueLink.erase (eval (source ops owners) (p053 owners ops master masterKey checkpoint checkpointKey lane laneKey live) ()) =
 v053 owners ops master masterKey checkpoint checkpointKey lane laneKey live := by
 unfold p053 v053
 rw [NMX_S053.step]
 simp only [NMX_Fold05.e054]
#print axioms e053

def p052 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.snapshot ⟨snapshotPool,master.payload.identity.deployment_domain,
  lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
  lane.payload.tree.root,lane.payload.tree.frontier⟩)) (fun live =>
  NMX_Fold05.p053 owners ops master masterKey checkpoint checkpointKey lane laneKey live)
def v052 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) : Final :=
  (fun live =>
  NMX_Fold05.v053 owners ops master masterKey checkpoint checkpointKey lane laneKey live) ⟨owners.snapshot,⟨snapshotPool,master.payload.identity.deployment_domain,
  lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
  lane.payload.tree.root,lane.payload.tree.frontier⟩⟩
theorem e052 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) :
 NMX_ValueLink.erase (eval (source ops owners) (p052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool) ()) =
 v052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool := by
 unfold p052 v052
 rw [NMX_S052.step]
 simp only [NMX_Fold05.e053]
#print axioms e052

def p051 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun snapshotPool =>
  NMX_Fold05.p052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool)
def v051 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) : Final :=
  (ops.op39 masterKey) >>= fun value => (fun snapshotPool =>
  NMX_Fold05.v052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool) value
theorem e051 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p051 owners ops master masterKey checkpoint checkpointKey lane laneKey) ()) =
 v051 owners ops master masterKey checkpoint checkpointKey lane laneKey := by
 unfold p051 v051
 rw [NMX_S051.step]
 simp only [NMX_Fold05.e052]
#print axioms e051
end NMX_Fold05
end
