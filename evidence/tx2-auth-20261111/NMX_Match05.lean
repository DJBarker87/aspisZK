import NMX_BindCongruence
import NMX_PdaMap
import NMX_Actual05
import NMX_Fold05
set_option autoImplicit false
noncomputable section
namespace NMX_Match05
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

/-- Actual emitted occurrence 55; complete arbitrary reply/control arms. -/
theorem e055 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) :
 NMX_Fold05.v055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes =
 NMX_Actual05.t055 owners ops master.payload checkpoint.payload lane.payload laneKey live.payload returnedMasterBytes returnedCheckpointBytes := by
 unfold NMX_Fold05.v055 NMX_Actual05.t055
 apply NMX_BindCongruence.step
 intro returnedLaneBytes
 rfl
#print axioms e055

/-- Actual emitted occurrence 54; complete arbitrary reply/control arms. -/
theorem e054 (owners : Owners) (ops : Ops) (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) :
 NMX_Fold05.v054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes =
 NMX_Actual05.t054 owners ops master.payload checkpoint.payload checkpointKey lane.payload laneKey live.payload returnedMasterBytes := by
 unfold NMX_Fold05.v054 NMX_Actual05.t054
 apply NMX_BindCongruence.step
 intro returnedCheckpointBytes
 exact NMX_Match05.e055 owners ops master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes
#print axioms e054

/-- Actual emitted occurrence 53; complete arbitrary reply/control arms. -/
theorem e053 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) :
 NMX_Fold05.v053 owners ops master masterKey checkpoint checkpointKey lane laneKey live =
 NMX_Actual05.t053 owners ops master.payload masterKey checkpoint.payload checkpointKey lane.payload laneKey live.payload := by
 unfold NMX_Fold05.v053 NMX_Actual05.t053
 apply NMX_BindCongruence.step
 intro returnedMasterBytes
 exact NMX_Match05.e054 owners ops master checkpoint checkpointKey lane laneKey live returnedMasterBytes
#print axioms e053

/-- Actual emitted occurrence 52; complete arbitrary reply/control arms. -/
theorem e052 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) :
 NMX_Fold05.v052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool =
 NMX_Actual05.t052 owners ops master.payload masterKey checkpoint.payload checkpointKey lane.payload laneKey snapshotPool := by
 unfold NMX_Fold05.v052 NMX_Actual05.t052
 let live : Box Snapshot := ⟨owners.snapshot,⟨snapshotPool,master.payload.identity.deployment_domain,
  lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
  lane.payload.tree.root,lane.payload.tree.frontier⟩⟩
 exact NMX_Match05.e053 owners ops master masterKey checkpoint checkpointKey lane laneKey live
#print axioms e052

/-- Actual emitted occurrence 51; complete arbitrary reply/control arms. -/
theorem e051 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) :
 NMX_Fold05.v051 owners ops master masterKey checkpoint checkpointKey lane laneKey =
 NMX_Actual05.t051 owners ops master.payload masterKey checkpoint.payload checkpointKey lane.payload laneKey := by
 unfold NMX_Fold05.v051 NMX_Actual05.t051
 apply NMX_BindCongruence.step
 intro snapshotPool
 exact NMX_Match05.e052 owners ops master masterKey checkpoint checkpointKey lane laneKey snapshotPool
#print axioms e051
end NMX_Match05
end
