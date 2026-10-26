import PoolS2_PrefixSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PdaSource
open Aeneas Aeneas.Std Result
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev PdaError := AdapterRw.solana_pubkey.PubkeyError
abbrev Master := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
/-- Only actual SDK PDA children. No caller success/output/frame law is a field.
Their source/runtime/oracle interpretation remains an existing open boundary. -/
structure Ops where
  create : Slice (Slice U8) → Key → Result (core.result.Result Key PdaError)
  find : Slice (Slice U8) → Key → Result (Key × U8)

def asRef (key : Key) : Result (Slice U8) := ok ⟨key.val,key.property.le⟩
def laneCount : Result Usize := ok 8#usize
def masterSeed : Result (Slice U8) := ok ⟨[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,109#u8,97#u8,115#u8,116#u8,101#u8,114#u8,45#u8,118#u8,49#u8],by decide⟩
def laneSeed : Result (Slice U8) := ok ⟨[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,108#u8,97#u8,110#u8,101#u8,45#u8,118#u8,49#u8],by decide⟩
def checkpointSeed : Result (Slice U8) := ok ⟨[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8,45#u8,118#u8,49#u8],by decide⟩

def pair_forest.pool_v1_pair_forest_master_address (ops : Ops)
  (program_id : Key) (asset_mint : Key) :
  Result (Key × Std.U8)
  := do
  let s ← masterSeed
  let s1 ←
    asRef asset_mint
  let s2 ← lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))
  ops.find s2 program_id

/-- [aspis_pool::pair_forest::pool_v1_pair_forest_lane_address]:
    Source: 'programs/aspis-pool/src/pair_forest.rs', lines 321:0-333:1
    Visibility: public -/
def pair_forest.pool_v1_pair_forest_lane_address (ops : Ops)
  (program_id : Key) (master : Key)
  (lane_id : Std.U8) :
  Result (core.result.Result (Key × Std.U8)
    AdapterRw.solana_program_error.ProgramError)
  := do
  let i ← lift (core.convert.num.FromUsizeU8.from lane_id)
  let i1 ←
    laneCount
  if i >= i1
  then
    ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidSeeds)
  else
    let s ← laneSeed
    let s1 ← asRef master
    let s2 ← lift (Array.to_slice (Array.make 1#usize [ lane_id ]))
    let s3 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, s2 ]))
    let p ← ops.find s3 program_id
    ok (core.result.Result.Ok p)

/-- [aspis_pool::pair_forest::pool_v1_pair_forest_checkpoint_address]:
    Source: 'programs/aspis-pool/src/pair_forest.rs', lines 335:0-348:1
    Visibility: public -/
def pair_forest.pool_v1_pair_forest_checkpoint_address (ops : Ops)
  (program_id : Key) (master : Key)
  (checkpoint_sequence : Std.U64) :
  Result (Key × Std.U8)
  := do
  let s ← checkpointSeed
  let s1 ← asRef master
  let a ← lift (core.num.U64.to_le_bytes checkpoint_sequence)
  let s2 ← lift (Array.to_slice a)
  let s3 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, s2 ]))
  ops.find s3 program_id

def registry.stored_bump_address_matches (ops : Ops)
    (seeds_with_bump : Slice (Slice U8)) (program_id key : Key) : Result Bool := do
  let r ← ops.create seeds_with_bump program_id
  match r with
  | .Err _ => ok false
  | .Ok address => Hist_Authority.keyEq address key

/-- [aspis_pool::pair_forest::master_address_matches]:
    Source: 'programs/aspis-pool/src/pair_forest.rs', lines 453:0-467:1 -/
def pair_forest.master_address_matches (ops : Ops)
  (program_id : Key)
  (master :
  Master)
  (key : Key) :
  Result Bool
  := do
  let s ← masterSeed
  let s1 ← lift (Array.to_slice master.identity.asset_mint)
  let s2 ← lift (Array.to_slice (Array.make 1#usize [ master.bump ]))
  let s3 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, s2 ]))
  registry.stored_bump_address_matches ops s3 program_id key

/-- [aspis_pool::pair_forest::lane_address_matches]:
    Source: 'programs/aspis-pool/src/pair_forest.rs', lines 470:0-490:1 -/
def pair_forest.lane_address_matches (ops : Ops)
  (program_id : Key) (master : Key)
  (lane_id : Std.U8) (bump : Std.U8) (key : Key) :
  Result (core.result.Result Bool AdapterRw.solana_program_error.ProgramError)
  := do
  let i ← lift (core.convert.num.FromUsizeU8.from lane_id)
  let i1 ←
    laneCount
  if i >= i1
  then
    ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidSeeds)
  else
    let s ← laneSeed
    let s1 ← asRef master
    let s2 ← lift (Array.to_slice (Array.make 1#usize [ lane_id ]))
    let s3 ← lift (Array.to_slice (Array.make 1#usize [ bump ]))
    let s4 ← lift (Array.to_slice (Array.make 4#usize [ s, s1, s2, s3 ]))
    let b ← registry.stored_bump_address_matches ops s4 program_id key
    ok (core.result.Result.Ok b)

#print axioms registry.stored_bump_address_matches
#print axioms pair_forest.master_address_matches
#print axioms pair_forest.lane_address_matches
#print axioms pair_forest.pool_v1_pair_forest_checkpoint_address
end AspisR1.PoolS2_PdaSource
end
