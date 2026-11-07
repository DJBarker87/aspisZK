import NMX_R2_CanonicalTarget
import NMX_R2_CB01
set_option autoImplicit false
namespace NMX_R2_CB00
open RSL

def r010 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (verifierCheckpoint : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.ofExcept (RSL.readonlyAccount masterAccount pool)) (fun _unit =>
  NMX_R2_CB01.r011 L D verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def r009 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (verifierCheckpoint : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.verifierCheckpoint verifierCheckpoint verifier false) (fun _unit =>
  NMX_R2_CB00.r010 L D verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def r008 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) (verifierCheckpoint : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.ofExcept (RSL.readonlyBuffer proof)) (fun _unit =>
  NMX_R2_CB00.r009 L D verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def r007 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (accounts : List RSL.OwnedAccount) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) (entryAccount : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.index accounts 6) (fun verifierCheckpoint =>
  NMX_R2_CB00.r008 L D verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def r006 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (accounts : List RSL.OwnedAccount) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) (registryAccount : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.index accounts 5) (fun entryAccount =>
  NMX_R2_CB00.r007 L D verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount)

def r005 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (accounts : List RSL.OwnedAccount) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) (laneAccount : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.index accounts 4) (fun registryAccount =>
  NMX_R2_CB00.r006 L D verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount)

def r004 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (accounts : List RSL.OwnedAccount) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) (checkpointAccount : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.index accounts 3) (fun laneAccount =>
  NMX_R2_CB00.r005 L D verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount)

def r003 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (accounts : List RSL.OwnedAccount) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) (masterAccount : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.index accounts 2) (fun checkpointAccount =>
  NMX_R2_CB00.r004 L D verifier accounts pool outputLane slot proof masterAccount checkpointAccount)

def r002 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (accounts : List RSL.OwnedAccount) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) (proof : RSL.OwnedAccount) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.index accounts 1) (fun masterAccount =>
  NMX_R2_CB00.r003 L D verifier accounts pool outputLane slot proof masterAccount)

def r001 (L : RSL.PoolLib) (D : RSL.DeployedIds) (verifier : RSL.B32) (accounts : List RSL.OwnedAccount) (pool : RSL.B32) (outputLane : UInt8) (slot : UInt64) : RSL.RS RSL.Authenticated :=
 RSL.RS.bind (RSL.RS.index accounts 0) (fun proof =>
  NMX_R2_CB00.r002 L D verifier accounts pool outputLane slot proof)
end NMX_R2_CB00
