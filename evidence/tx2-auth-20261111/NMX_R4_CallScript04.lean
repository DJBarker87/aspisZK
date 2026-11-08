import NMX_R4_CallProgram
import NMX_ResultSteps
import NMX_R4_CallScript05
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallScript04
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram

def t050 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) : Program (core.result.Result Auth PE) := do
  if wrongLanePda
  then
    Program.ret (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_R4_CallScript05.t051 owners ops master masterKey checkpoint checkpointKey lane laneKey

def t049 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let wrongLanePda ← scalar (core.cmp.PartialEq.ne.trait_default
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      derivedLane laneKey)
  NMX_R4_CallScript04.t050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda

def t048 (owners : Owners) (ops : Ops) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let laneKey ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key
      laneAccount)
  NMX_R4_CallScript04.t049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey

def t047 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) : Program (core.result.Result Auth PE) := do
  let r17 ← pda laneSeeds pool
  let r18 ← scalar (core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r17 ())
  let cf15 ← scalar (core.result.Result.Insts.CoreOpsTry.branch
      r18)
  match cf15 with
  |
    core.ops.control_flow.ControlFlow.Continue
    derivedLane =>
    NMX_R4_CallScript04.t048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual)

def t046 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program (core.result.Result Auth PE) := do
  let laneMasterSeed ← scalar (ops.op40
      masterKey)
  let laneIdSeed ← scalar (.ok (Array.to_slice
      (Array.make 1#usize [
        outputLane
        ])))
  let laneBump ← scalar (.ok (Array.to_slice
      (Array.make 1#usize [
        lane.payload.bump
        ])))
  let laneSeeds ← scalar (.ok (Array.to_slice
      (Array.make 4#usize [
        r1_pool_adapter.PAIR_FOREST_LANE_SEED,
        laneMasterSeed, laneIdSeed, laneBump
        ])))
  NMX_R4_CallScript04.t047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds

def t045 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program (core.result.Result Auth PE) := do
  if lane.payload.lane_id != outputLane
  then
    Program.ret (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_R4_CallScript04.t046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane

def t044 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) : Program (core.result.Result Auth PE) := do
  if wrongLaneMaster
  then
    Program.ret (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_R4_CallScript04.t045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane

def t043 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) : Program (core.result.Result Auth PE) := do
  let wrongLaneMaster ← scalar (core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8
      lane.payload.master laneMasterBytes)
  NMX_R4_CallScript04.t044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster

def t042 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program (core.result.Result Auth PE) := do
  let laneMasterBytes ← scalar (ops.op39 masterKey)
  NMX_R4_CallScript04.t043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes

def t041 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) : Program (core.result.Result Auth PE) := do
  let r16 ← child (.lane laneBytes)
  let cf14 ← scalar (core.result.Result.Insts.CoreOpsTry.branch
      r16)
  match cf14 with
  |
    core.ops.control_flow.ControlFlow.Continue
    lane =>
    NMX_R4_CallScript04.t042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual)
end NMX_R4_CallScript04
end
