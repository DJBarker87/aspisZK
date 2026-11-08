import NMX_R4_CallProgram
import NMX_ResultSteps
import NMX_R4_CallScript04
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallScript03
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram

def t040 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let r15 ← child (.data laneAccount)
  let cf13 ← scalar (core.result.Result.Insts.CoreOpsTry.branch
      r15)
  match cf13 with
  |
    core.ops.control_flow.ControlFlow.Continue
    laneBytes =>
    NMX_R4_CallScript04.t041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual)

def t039 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) : Program (core.result.Result Auth PE) := do
  if wrongCheckpointPda
  then
    Program.ret (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_R4_CallScript03.t040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey

def t038 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let wrongCheckpointPda ← scalar (core.cmp.PartialEq.ne.trait_default
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      derivedCheckpoint checkpointKey)
  NMX_R4_CallScript03.t039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda

def t037 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let checkpointKey ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key
      checkpointAccount)
  NMX_R4_CallScript03.t038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey

def t036 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) : Program (core.result.Result Auth PE) := do
  let r13 ← pda checkpointSeeds pool
  let r14 ← scalar (core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r13 ())
  let cf12 ← scalar (core.result.Result.Insts.CoreOpsTry.branch
      r14)
  match cf12 with
  |
    core.ops.control_flow.ControlFlow.Continue
    derivedCheckpoint =>
    NMX_R4_CallScript03.t037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual)

def t035 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program (core.result.Result Auth PE) := do
  let checkpointMasterSeed ← scalar (ops.op40
      masterKey)
  let sequenceBytes ← scalar (.ok (core.num.U64.to_le_bytes
      checkpoint.payload.checkpoint_sequence))
  let sequenceSeed ← scalar (.ok (Array.to_slice sequenceBytes))
  let checkpointBump ← scalar (.ok (Array.to_slice
      (Array.make 1#usize [ checkpoint.payload.bump ])))
  let checkpointSeeds ← scalar (.ok (Array.to_slice
      (Array.make 4#usize [
        r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,
        checkpointMasterSeed, sequenceSeed, checkpointBump
        ])))
  NMX_R4_CallScript03.t036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds

def t034 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) : Program (core.result.Result Auth PE) := do
  if wrongDeployment
  then
    Program.ret (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_R4_CallScript03.t035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint

def t033 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program (core.result.Result Auth PE) := do
  let wrongDeployment ← scalar (core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8
      checkpoint.payload.deployment_domain
      master.payload.identity.deployment_domain)
  NMX_R4_CallScript03.t034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment

def t032 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) : Program (core.result.Result Auth PE) := do
  if wrongCheckpointMaster
  then
    Program.ret (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_R4_CallScript03.t033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint

def t031 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) : Program (core.result.Result Auth PE) := do
  let wrongCheckpointMaster ← scalar (core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8 checkpoint.payload.master checkpointMasterBytes)
  NMX_R4_CallScript03.t032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster
end NMX_R4_CallScript03
end
