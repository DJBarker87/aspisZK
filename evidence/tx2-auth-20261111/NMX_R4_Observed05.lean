import NMX_R4_CallContext
import NMX_R4_PdaObservation
import NMX_R4_CallScript05
import NMX_Fold05
set_option autoImplicit false
noncomputable section
namespace NMX_R4_Observed05
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallRun NMX_R4_CallContext

theorem e055 (c : Context) (master : Box Master) (checkpoint : Box Checkpoint) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) (returnedCheckpointBytes : Array U8 32#usize) :
 observe c (NMX_R4_CallScript05.t055 c.owners (ops c) master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold05.p055 c.owners (ops c) master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes) := by
 unfold NMX_R4_CallScript05.t055 NMX_Fold05.p055
 apply NMX_R4_ObservedStep.scalar
 intro returnedLaneBytes
 rfl
#print axioms e055

theorem e054 (c : Context) (master : Box Master) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) (returnedMasterBytes : Array U8 32#usize) :
 observe c (NMX_R4_CallScript05.t054 c.owners (ops c) master checkpoint checkpointKey lane laneKey live returnedMasterBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold05.p054 c.owners (ops c) master checkpoint checkpointKey lane laneKey live returnedMasterBytes) := by
 unfold NMX_R4_CallScript05.t054 NMX_Fold05.p054
 apply NMX_R4_ObservedStep.scalar
 intro returnedCheckpointBytes
 exact NMX_R4_Observed05.e055 c master checkpoint lane laneKey live returnedMasterBytes returnedCheckpointBytes
#print axioms e054

theorem e053 (c : Context) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (live : Box Snapshot) :
 observe c (NMX_R4_CallScript05.t053 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey live) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold05.p053 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey live) := by
 unfold NMX_R4_CallScript05.t053 NMX_Fold05.p053
 apply NMX_R4_ObservedStep.scalar
 intro returnedMasterBytes
 exact NMX_R4_Observed05.e054 c master checkpoint checkpointKey lane laneKey live returnedMasterBytes
#print axioms e053

theorem e052 (c : Context) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (snapshotPool : Array U8 32#usize) :
 observe c (NMX_R4_CallScript05.t052 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey snapshotPool) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold05.p052 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey snapshotPool) := by
 unfold NMX_R4_CallScript05.t052 NMX_Fold05.p052
 apply NMX_R4_ObservedStep.snapshot
 intro live
 exact NMX_R4_Observed05.e053 c master masterKey checkpoint checkpointKey lane laneKey live
#print axioms e052

theorem e051 (c : Context) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript05.t051 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold05.p051 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey) := by
 unfold NMX_R4_CallScript05.t051 NMX_Fold05.p051
 apply NMX_R4_ObservedStep.scalar
 intro snapshotPool
 exact NMX_R4_Observed05.e052 c master masterKey checkpoint checkpointKey lane laneKey snapshotPool
#print axioms e051
end NMX_R4_Observed05
end
