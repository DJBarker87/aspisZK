import NMX_Skeleton
import NMX_SF04
set_option autoImplicit false
noncomputable section
namespace NMX_SF03
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceProgram
attribute [local instance] Classical.propDecidable

def p040 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.data laneAccount)) (fun laneBytes =>
  NMX_SF04.p041 pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes)

def p039 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongCheckpointPda) (fun _unit =>
  NMX_SF03.p040 pool outputLane laneAccount master masterKey checkpoint checkpointKey)

def p038 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw ((.ok (!(decide (derivedCheckpoint = checkpointKey)))))) (fun wrongCheckpointPda =>
  NMX_SF03.p039 pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda)

def p037 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.key checkpointAccount)) (fun checkpointKey =>
  NMX_SF03.p038 pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey)

def p036 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.pda checkpointSeeds pool)) (fun derivedCheckpoint =>
  NMX_SF03.p037 pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint)

def p035 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.asRef masterKey)) (fun checkpointMasterSeed =>
  let sequenceSeed := Array.to_slice (core.num.U64.to_le_bytes checkpoint.payload.checkpoint_sequence)
  let checkpointBump := Array.to_slice (Array.make 1#usize [checkpoint.payload.bump])
  let checkpointSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,checkpointMasterSeed,sequenceSeed,checkpointBump])
  NMX_SF03.p036 pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds)

def p034 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongDeployment) (fun _unit =>
  NMX_SF03.p035 pool outputLane checkpointAccount laneAccount master masterKey checkpoint)

def p033 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  checkpoint.payload.deployment_domain master.payload.identity.deployment_domain)) (fun wrongDeployment =>
  NMX_SF03.p034 pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment)

def p032 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongCheckpointMaster) (fun _unit =>
  NMX_SF03.p033 pool outputLane checkpointAccount laneAccount master masterKey checkpoint)

def p031 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  checkpoint.payload.master checkpointMasterBytes)) (fun wrongCheckpointMaster =>
  NMX_SF03.p032 pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster)
end NMX_SF03
end
