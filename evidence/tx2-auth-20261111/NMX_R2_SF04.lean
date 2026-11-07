import NMX_R2_Skeleton
import NMX_R2_SF05
set_option autoImplicit false
noncomputable section
namespace NMX_R2_SF04
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceProgram
attribute [local instance] Classical.propDecidable

def p050 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongLanePda) (fun _unit =>
  NMX_R2_SF05.p051 master masterKey checkpoint checkpointKey lane laneKey)

def p049 (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw ((.ok (!(decide (derivedLane = laneKey)))))) (fun wrongLanePda =>
  NMX_R2_SF04.p050 master masterKey checkpoint checkpointKey lane laneKey wrongLanePda)

def p048 (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.key laneAccount)) (fun laneKey =>
  NMX_R2_SF04.p049 master masterKey checkpoint checkpointKey lane derivedLane laneKey)

def p047 (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.pda laneSeeds pool)) (fun derivedLane =>
  NMX_R2_SF04.p048 laneAccount master masterKey checkpoint checkpointKey lane derivedLane)

def p046 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.asRef masterKey)) (fun laneMasterSeed =>
  let laneIdSeed := Array.to_slice (Array.make 1#usize [outputLane])
  let laneBump := Array.to_slice (Array.make 1#usize [lane.payload.bump])
  let laneSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_LANE_SEED,laneMasterSeed,laneIdSeed,laneBump])
  NMX_R2_SF04.p047 pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds)

def p045 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check (lane.payload.lane_id != outputLane)) (fun _unit =>
  NMX_R2_SF04.p046 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)

def p044 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongLaneMaster) (fun _unit =>
  NMX_R2_SF04.p045 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)

def p043 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  lane.payload.master laneMasterBytes)) (fun wrongLaneMaster =>
  NMX_R2_SF04.p044 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster)

def p042 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun laneMasterBytes =>
  NMX_R2_SF04.p043 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes)

def p041 (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.lane laneBytes)) (fun lane =>
  NMX_R2_SF04.p042 pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)
end NMX_R2_SF04
end
