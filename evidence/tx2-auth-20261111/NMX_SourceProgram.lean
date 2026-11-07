import NMX_Program
import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NMX_SourceProgram
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program
abbrev P := Program
abbrev C := Command
def call {A : Type} (c : C A) : P A := .step c .ret
def raw {A : Type} (a : Result A) : P A := call (.raw a)
def check (condition : Bool) : P Unit :=
 if condition then .reject .InvalidAccountData else .ret ()
/-- Literal source control order at frozen233. Boxes stay owned at every local
and returned value. Commands retain all runtime/child arguments; no child
success is assumed. The value projection is checked separately against E002. -/
def auth (ops : Ops) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) : P Auth := do
 if Slice.len accounts != 7#usize then
  if Slice.len accounts < 7#usize then .reject .NotEnoughAccountKeys
  else .reject .InvalidArgument
 else
  let proof ← raw (Slice.index_usize accounts 0#usize)
  let masterAccount ← raw (Slice.index_usize accounts 1#usize)
  let checkpointAccount ← raw (Slice.index_usize accounts 2#usize)
  let laneAccount ← raw (Slice.index_usize accounts 3#usize)
  let registryAccount ← raw (Slice.index_usize accounts 4#usize)
  let entryAccount ← raw (Slice.index_usize accounts 5#usize)
  let verifierCheckpoint ← raw (Slice.index_usize accounts 6#usize)
  call (.readonlyBuffer proof)
  call (.checkpointGuard verifierCheckpoint verifier false)
  call (.readonlyAccount masterAccount pool)
  call (.readonlyAccount checkpointAccount pool)
  call (.readonlyAccount laneAccount pool)
  call (.distinct (Array.make 7#usize [proof,masterAccount,checkpointAccount,
    laneAccount,registryAccount,entryAccount,verifierCheckpoint]))
  let masterBytes ← call (.data masterAccount)
  let master ← call (.master masterBytes)
  let masterKey ← call (.key masterAccount)
  let masterKeyBytes ← call (.toBytes masterKey)
  let wrongMaster ← raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    master.payload.identity.pool masterKeyBytes)
  check wrongMaster
  let allLanes ← raw ops.op16
  check (master.payload.initialized_lane_mask != allLanes)
  let mintKey ← call (.fromBytes master.payload.identity.asset_mint)
  let mintSeed ← call (.asRef mintKey)
  let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
  let masterSeeds := Array.to_slice (Array.make 3#usize [
    r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
  let derivedMaster ← call (.pda masterSeeds pool)
  let wrongMasterPda ← raw (core.cmp.PartialEq.ne.trait_default
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedMaster masterKey)
  check wrongMasterPda
  call (.registry verifier pool masterAccount master.payload registryAccount entryAccount slot)
  let checkpointBytes ← call (.data checkpointAccount)
  let checkpoint ← call (.checkpoint checkpointBytes)
  let checkpointMasterBytes ← call (.toBytes masterKey)
  let wrongCheckpointMaster ← raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    checkpoint.payload.master checkpointMasterBytes)
  check wrongCheckpointMaster
  let wrongDeployment ← raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    checkpoint.payload.deployment_domain master.payload.identity.deployment_domain)
  check wrongDeployment
  let checkpointMasterSeed ← call (.asRef masterKey)
  let sequenceSeed := Array.to_slice (core.num.U64.to_le_bytes checkpoint.payload.checkpoint_sequence)
  let checkpointBump := Array.to_slice (Array.make 1#usize [checkpoint.payload.bump])
  let checkpointSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,checkpointMasterSeed,sequenceSeed,checkpointBump])
  let derivedCheckpoint ← call (.pda checkpointSeeds pool)
  let checkpointKey ← call (.key checkpointAccount)
  let wrongCheckpointPda ← raw (core.cmp.PartialEq.ne.trait_default
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedCheckpoint checkpointKey)
  check wrongCheckpointPda
  let laneBytes ← call (.data laneAccount)
  let lane ← call (.lane laneBytes)
  let laneMasterBytes ← call (.toBytes masterKey)
  let wrongLaneMaster ← raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    lane.payload.master laneMasterBytes)
  check wrongLaneMaster
  check (lane.payload.lane_id != outputLane)
  let laneMasterSeed ← call (.asRef masterKey)
  let laneIdSeed := Array.to_slice (Array.make 1#usize [outputLane])
  let laneBump := Array.to_slice (Array.make 1#usize [lane.payload.bump])
  let laneSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_LANE_SEED,laneMasterSeed,laneIdSeed,laneBump])
  let derivedLane ← call (.pda laneSeeds pool)
  let laneKey ← call (.key laneAccount)
  let wrongLanePda ← raw (core.cmp.PartialEq.ne.trait_default
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedLane laneKey)
  check wrongLanePda
  let snapshotPool ← call (.toBytes masterKey)
  let live ← call (.snapshot ⟨snapshotPool,master.payload.identity.deployment_domain,
    lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
    lane.payload.tree.root,lane.payload.tree.frontier⟩)
  let returnedMasterBytes ← call (.toBytes masterKey)
  let returnedCheckpointBytes ← call (.toBytes checkpointKey)
  let returnedLaneBytes ← call (.toBytes laneKey)
  pure ⟨returnedMasterBytes,returnedCheckpointBytes,returnedLaneBytes,master,checkpoint,lane,live⟩
end NMX_SourceProgram
end
