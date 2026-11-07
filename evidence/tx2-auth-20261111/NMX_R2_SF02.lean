import NMX_R2_Skeleton
import NMX_R2_SF03
set_option autoImplicit false
noncomputable section
namespace NMX_R2_SF02
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceProgram
attribute [local instance] Classical.propDecidable

def p030 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun checkpointMasterBytes =>
  NMX_R2_SF03.p031 pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes)

def p029 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.checkpoint checkpointBytes)) (fun checkpoint =>
  NMX_R2_SF02.p030 pool outputLane checkpointAccount laneAccount master masterKey checkpoint)

def p028 (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.data checkpointAccount)) (fun checkpointBytes =>
  NMX_R2_SF02.p029 pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes)

def p027 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.registry verifier pool masterAccount master.payload registryAccount entryAccount slot)) (fun _unit =>
  NMX_R2_SF02.p028 pool outputLane checkpointAccount laneAccount master masterKey)

def p026 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongMasterPda) (fun _unit =>
  NMX_R2_SF02.p027 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)

def p025 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw ((.ok (!(decide (derivedMaster = masterKey)))))) (fun wrongMasterPda =>
  NMX_R2_SF02.p026 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda)

def p024 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.pda masterSeeds pool)) (fun derivedMaster =>
  NMX_R2_SF02.p025 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster)

def p023 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.asRef mintKey)) (fun mintSeed =>
  let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
  let masterSeeds := Array.to_slice (Array.make 3#usize [
    r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
  NMX_R2_SF02.p024 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds)

def p022 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.fromBytes master.payload.identity.asset_mint)) (fun mintKey =>
  NMX_R2_SF02.p023 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey)

def p021 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check (master.payload.initialized_lane_mask != allLanes)) (fun _unit =>
  NMX_R2_SF02.p022 verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)
end NMX_R2_SF02
end
