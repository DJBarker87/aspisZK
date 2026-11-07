import NMX_SourceProgram
import NMX_R2_PrimitiveInstall
set_option autoImplicit false
noncomputable section
namespace NMX_R2_Skeleton
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceProgram
attribute [local instance] Classical.propDecidable
/-- Source program with its two primitive condition slots interpreted. No
operation dictionary or child-return placeholder is a parameter. -/
def auth (verifier : solana_pubkey.Pubkey)
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
  let allLanes ← raw (.ok 255#u8)
  check (master.payload.initialized_lane_mask != allLanes)
  let mintKey ← call (.fromBytes master.payload.identity.asset_mint)
  let mintSeed ← call (.asRef mintKey)
  let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
  let masterSeeds := Array.to_slice (Array.make 3#usize [
    r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
  let derivedMaster ← call (.pda masterSeeds pool)
  let wrongMasterPda ← raw ((.ok (!(decide (derivedMaster = masterKey)))))
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
  let wrongCheckpointPda ← raw ((.ok (!(decide (derivedCheckpoint = checkpointKey)))))
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
  let wrongLanePda ← raw ((.ok (!(decide (derivedLane = laneKey)))))
  check wrongLanePda
  let snapshotPool ← call (.toBytes masterKey)
  let live ← call (.snapshot ⟨snapshotPool,master.payload.identity.deployment_domain,
    lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
    lane.payload.tree.root,lane.payload.tree.frontier⟩)
  let returnedMasterBytes ← call (.toBytes masterKey)
  let returnedCheckpointBytes ← call (.toBytes checkpointKey)
  let returnedLaneBytes ← call (.toBytes laneKey)
  pure ⟨returnedMasterBytes,returnedCheckpointBytes,returnedLaneBytes,master,checkpoint,lane,live⟩

/-- Every field of the base dictionary is dead in this source term after the
named std condition installation. Child calls remain typed Commands. -/
theorem source (base : Ops) (env : RSL.Env) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_SourceProgram.auth (NMX_R2_PrimitiveInstall.install base env)
  verifier accounts pool outputLane slot = auth verifier accounts pool outputLane slot := by
 unfold NMX_SourceProgram.auth auth
 simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
  solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,NMX_R2_PrimitiveInstall.install,
  NMX_LeafInstall.install,NGL_CheckpointModel.install,Aeneas.Std.bind_tc_ok,decide_not,Bool.decide_eq_true]
#print axioms source
end NMX_R2_Skeleton
end
