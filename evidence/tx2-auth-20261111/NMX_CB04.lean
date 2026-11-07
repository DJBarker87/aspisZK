import NMX_CanonicalTarget
import NMX_CB05
set_option autoImplicit false
namespace NMX_CB04
open RSL

def r050 (L : RSL.PoolLib) (D : RSL.DeployedIds) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (laneKey : RSL.B32) (wrongLanePda : Bool) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check (wrongLanePda) .invalidAccountData) (fun _unit =>
  NMX_CB05.r051 L D master masterKey checkpoint checkpointKey lane laneKey)

def r049 (L : RSL.PoolLib) (D : RSL.DeployedIds) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (derivedLane : RSL.B32) (laneKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (decide (derivedLane ≠ laneKey))) (fun wrongLanePda =>
  NMX_CB04.r050 L D master masterKey checkpoint checkpointKey lane laneKey wrongLanePda)

def r048 (L : RSL.PoolLib) (D : RSL.DeployedIds) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (derivedLane : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure laneAccount.key) (fun laneKey =>
  NMX_CB04.r049 L D master masterKey checkpoint checkpointKey lane derivedLane laneKey)

def r047 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (laneSeeds : List RSL.Bytes) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.pdaOrErr laneSeeds pool) (fun derivedLane =>
  NMX_CB04.r048 L D laneAccount master masterKey checkpoint checkpointKey lane derivedLane)

def r046 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure masterKey.bytes) (fun laneMasterSeed =>
  let laneIdSeed := [outputLane]
  let laneBump := [lane.bump]
  let laneSeeds := [RSL.SEED_LANE,laneMasterSeed,laneIdSeed,laneBump]
  NMX_CB04.r047 L D pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds)

def r045 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check ((lane.lane_id != outputLane)) .invalidAccountData) (fun _unit =>
  NMX_CB04.r046 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)

def r044 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (wrongLaneMaster : Bool) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check (wrongLaneMaster) .invalidAccountData) (fun _unit =>
  NMX_CB04.r045 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)

def r043 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) (laneMasterBytes : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (decide (lane.master ≠ laneMasterBytes))) (fun wrongLaneMaster =>
  NMX_CB04.r044 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster)

def r042 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (lane : RSL.LaneState) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (masterKey)) (fun laneMasterBytes =>
  NMX_CB04.r043 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes)

def r041 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) (checkpointKey : RSL.B32) (laneBytes : RSL.Bytes) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.Spec.call RSL.TX2_217.Domain RSL.TX2_217.Ref laneBytes) (fun lane =>
  NMX_CB04.r042 L D pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)
end NMX_CB04
