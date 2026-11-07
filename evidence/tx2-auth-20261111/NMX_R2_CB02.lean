import NMX_R2_CanonicalTarget
import NMX_R2_CB03
set_option autoImplicit false
namespace NMX_R2_CB02
open RSL

def r030 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpoint : RSL.Checkpoint) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (masterKey)) (fun checkpointMasterBytes =>
  NMX_R2_CB03.r031 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes)

def r029 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (checkpointBytes : RSL.Bytes) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.decodeCheckpointBox L checkpointBytes) (fun checkpoint =>
  NMX_R2_CB02.r030 L D pool outputLane checkpointAccount laneAccount master masterKey checkpoint)

def r028 (L : RSL.PoolLib) (D : RSL.DeployedIds) (pool : RSL.B32) (outputLane : UInt8) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.OwnedAccount.data checkpointAccount) (fun checkpointBytes =>
  NMX_R2_CB02.r029 L D pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes)

def r027 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.Spec.call RSL.TX2_234.Domain (RSL.TX2_234.Ref L D) ⟨verifier,pool,masterAccount,master,registryAccount,entryAccount,slot⟩) (fun _unit =>
  NMX_R2_CB02.r028 L D pool outputLane checkpointAccount laneAccount master masterKey)

def r026 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (wrongMasterPda : Bool) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check (wrongMasterPda) .invalidAccountData) (fun _unit =>
  NMX_R2_CB02.r027 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)

def r025 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (derivedMaster : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (decide (derivedMaster ≠ masterKey))) (fun wrongMasterPda =>
  NMX_R2_CB02.r026 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda)

def r024 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (masterSeeds : List RSL.Bytes) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.pdaOrErr masterSeeds pool) (fun derivedMaster =>
  NMX_R2_CB02.r025 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster)

def r023 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (mintKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure mintKey.bytes) (fun mintSeed =>
  let bumpSeed := [master.bump]
  let masterSeeds := [RSL.SEED_MASTER,mintSeed,bumpSeed]
  NMX_R2_CB02.r024 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds)

def r022 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.pure (master.identity.asset_mint)) (fun mintKey =>
  NMX_R2_CB02.r023 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey)

def r021 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (master : RSL.Master) (masterKey : RSL.B32) (allLanes : UInt8) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.check ((master.initialized_lane_mask != allLanes)) .invalidAccountData) (fun _unit =>
  NMX_R2_CB02.r022 L D verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)
end NMX_R2_CB02
