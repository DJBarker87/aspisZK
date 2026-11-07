import NMX_R2_CanonicalTarget
import NMX_R2_CB02
set_option autoImplicit false
namespace NMX_R2_CB01
open RSL

def r020 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure RSL.ALL_LANES_MASK) (fun allLanes =>
  NMX_R2_CB02.r021 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes)

def r019 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (wrongMaster : Bool) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check (wrongMaster) .invalidAccountData) (fun _unit =>
  NMX_R2_CB01.r020 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)

def r018 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (masterKeyBytes : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (decide (master.identity.pool ≠ masterKeyBytes))) (fun wrongMaster =>
  NMX_R2_CB01.r019 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster)

def r017 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (masterKey)) (fun masterKeyBytes =>
  NMX_R2_CB01.r018 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes)

def r016 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure masterAccount.key) (fun masterKey =>
  NMX_R2_CB01.r017 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)

def r015 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (masterBytes : RSL.Bytes) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.decodeMasterBox L masterBytes) (fun master =>
  NMX_R2_CB01.r016 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master)

def r014 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.OwnedAccount.data masterAccount) (fun masterBytes =>
  NMX_R2_CB01.r015 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes)

def r013 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (verifierCheckpoint : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.ofExcept (RSL.requireDistinct [proof,masterAccount,checkpointAccount,laneAccount,registryAccount,entryAccount,verifierCheckpoint])) (fun _unit =>
  NMX_R2_CB01.r014 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount)

def r012 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (verifierCheckpoint : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.ofExcept (RSL.readonlyAccount laneAccount pool)) (fun _unit =>
  NMX_R2_CB01.r013 L D verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def r011 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (verifierCheckpoint : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.ofExcept (RSL.readonlyAccount checkpointAccount pool)) (fun _unit =>
  NMX_R2_CB01.r012 L D verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)
end NMX_R2_CB01
