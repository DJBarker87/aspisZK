import NMX_ResultSteps
import NMX_Actual05
set_option autoImplicit false
noncomputable section
namespace NMX_Actual04
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

def t050 (owners : Owners) (ops : Ops) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) : Final := do
  if wrongLanePda
  then
    ok
      (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual05.t051 owners ops master masterKey checkpoint checkpointKey lane laneKey

def t049 (owners : Owners) (ops : Ops) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) : Final := do
  let wrongLanePda ←
    core.cmp.PartialEq.ne.trait_default
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      derivedLane laneKey
  NMX_Actual04.t050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda

def t048 (owners : Owners) (ops : Ops) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (derivedLane : solana_pubkey.Pubkey) : Final := do
  let laneKey ←
    r1_pool_adapter.owned.OwnedAccount.impl.key
      laneAccount
  NMX_Actual04.t049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey

def t047 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (laneSeeds : Slice (Slice U8)) : Final := do
  let r17 ←
    ops.op38
      laneSeeds pool
  let r18 ←
    core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r17 ()
  let cf15 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r18
  match cf15 with
  |
    core.ops.control_flow.ControlFlow.Continue
    derivedLane =>
    NMX_Actual04.t048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

def t046 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) : Final := do
  let laneMasterSeed ←
    ops.op40
      masterKey
  let laneIdSeed ←
    lift (Array.to_slice
      (Array.make 1#usize [
        outputLane
        ]))
  let laneBump ←
    lift (Array.to_slice
      (Array.make 1#usize [
        lane.bump
        ]))
  let laneSeeds ←
    lift (Array.to_slice
      (Array.make 4#usize [
        r1_pool_adapter.PAIR_FOREST_LANE_SEED,
        laneMasterSeed, laneIdSeed, laneBump
        ]))
  NMX_Actual04.t047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds

def t045 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) : Final := do
  if lane.lane_id != outputLane
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual04.t046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane

def t044 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (wrongLaneMaster : Bool) : Final := do
  if wrongLaneMaster
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual04.t045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane

def t043 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) (laneMasterBytes : Array U8 32#usize) : Final := do
  let wrongLaneMaster ←
    core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8
      lane.master laneMasterBytes
  NMX_Actual04.t044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster

def t042 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Lane) : Final := do
  let laneMasterBytes ←
    ops.op39 masterKey
  NMX_Actual04.t043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes

def t041 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) : Final := do
  let r16 ←
    ops.op50
      laneBytes
  let cf14 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r16
  match cf14 with
  |
    core.ops.control_flow.ControlFlow.Continue
    lane =>
    NMX_Actual04.t042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual
end NMX_Actual04
end
