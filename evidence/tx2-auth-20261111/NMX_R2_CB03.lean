import NMX_R2_CanonicalTarget
import NMX_R2_CB04
set_option autoImplicit false
namespace NMX_R2_CB03
open RSL

def r040 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.OwnedAccount.data laneAccount) (fun laneBytes =>
  NMX_R2_CB04.r041 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes)

def r039 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (wrongCheckpointPda : Bool) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check (wrongCheckpointPda) .invalidAccountData) (fun _unit =>
  NMX_R2_CB03.r040 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey)

def r038 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (derivedCheckpoint : RSL.B32) (checkpointKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (decide (derivedCheckpoint ≠ checkpointKey))) (fun wrongCheckpointPda =>
  NMX_R2_CB03.r039 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda)

def r037 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (derivedCheckpoint : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure checkpointAccount.key) (fun checkpointKey =>
  NMX_R2_CB03.r038 L D pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey)

def r036 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointSeeds : List RSL.Bytes) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.pdaOrErr checkpointSeeds pool) (fun derivedCheckpoint =>
  NMX_R2_CB03.r037 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint)

def r035 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure masterKey.bytes) (fun checkpointMasterSeed =>
  let sequenceSeed := RSL.u64le checkpoint.checkpoint_sequence
  let checkpointBump := [checkpoint.bump]
  let checkpointSeeds := [RSL.SEED_CHECKPOINT,checkpointMasterSeed,sequenceSeed,checkpointBump]
  NMX_R2_CB03.r036 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds)

def r034 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (wrongDeployment : Bool) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check (wrongDeployment) .invalidAccountData) (fun _unit =>
  NMX_R2_CB03.r035 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint)

def r033 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (decide (checkpoint.deployment_domain ≠ master.identity.deployment_domain))) (fun wrongDeployment =>
  NMX_R2_CB03.r034 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment)

def r032 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (wrongCheckpointMaster : Bool) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check (wrongCheckpointMaster) .invalidAccountData) (fun _unit =>
  NMX_R2_CB03.r033 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint)

def r031 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointMasterBytes : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (decide (checkpoint.master ≠ checkpointMasterBytes))) (fun wrongCheckpointMaster =>
  NMX_R2_CB03.r032 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster)
end NMX_R2_CB03
