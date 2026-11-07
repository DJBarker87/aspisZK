import NMX_ResultSteps
import NMX_Actual04
set_option autoImplicit false
noncomputable section
namespace NMX_Actual03
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

def t040 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) : Final := do
  let r15 ←
    (r1_pool_adapter.owned.OwnedAccount.data ops)
      laneAccount
  let cf13 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r15
  match cf13 with
  |
    core.ops.control_flow.ControlFlow.Continue
    laneBytes =>
    NMX_Actual04.t041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

def t039 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) : Final := do
  if wrongCheckpointPda
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual03.t040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey

def t038 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) : Final := do
  let wrongCheckpointPda ←
    core.cmp.PartialEq.ne.trait_default
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      derivedCheckpoint checkpointKey
  NMX_Actual03.t039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda

def t037 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) : Final := do
  let checkpointKey ←
    r1_pool_adapter.owned.OwnedAccount.impl.key
      checkpointAccount
  NMX_Actual03.t038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey

def t036 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointSeeds : Slice (Slice U8)) : Final := do
  let r13 ←
    ops.op38
      checkpointSeeds pool
  let r14 ←
    core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r13 ()
  let cf12 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r14
  match cf12 with
  |
    core.ops.control_flow.ControlFlow.Continue
    derivedCheckpoint =>
    NMX_Actual03.t037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

def t035 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) : Final := do
  let checkpointMasterSeed ←
    ops.op40
      masterKey
  let sequenceBytes ←
    lift (core.num.U64.to_le_bytes
      checkpoint.checkpoint_sequence)
  let sequenceSeed ← lift (Array.to_slice sequenceBytes)
  let checkpointBump ←
    lift (Array.to_slice
      (Array.make 1#usize [ checkpoint.bump ]))
  let checkpointSeeds ←
    lift (Array.to_slice
      (Array.make 4#usize [
        r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,
        checkpointMasterSeed, sequenceSeed, checkpointBump
        ]))
  NMX_Actual03.t036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds

def t034 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (wrongDeployment : Bool) : Final := do
  if wrongDeployment
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual03.t035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint

def t033 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) : Final := do
  let wrongDeployment ←
    core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8
      checkpoint.deployment_domain
      master.identity.deployment_domain
  NMX_Actual03.t034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment

def t032 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (wrongCheckpointMaster : Bool) : Final := do
  if wrongCheckpointMaster
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual03.t033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint

def t031 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) (checkpointMasterBytes : Array U8 32#usize) : Final := do
  let wrongCheckpointMaster ←
    core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8 checkpoint.master checkpointMasterBytes
  NMX_Actual03.t032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster
end NMX_Actual03
end
