import NMX_ResultSteps
import NMX_Actual03
set_option autoImplicit false
noncomputable section
namespace NMX_Actual02
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

def t030 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Checkpoint) : Final := do
  let checkpointMasterBytes ← ops.op39 masterKey
  NMX_Actual03.t031 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes

def t029 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) : Final := do
  let r12 ←
    ops.op49 checkpointBytes
  let cf11 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r12
  match cf11 with
  | core.ops.control_flow.ControlFlow.Continue
    checkpoint =>
    NMX_Actual02.t030 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError) residual

def t028 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) : Final := do
  let r11 ←
    (r1_pool_adapter.owned.OwnedAccount.data ops)
      checkpointAccount
  let cf10 ←
    core.result.Result.Insts.CoreOpsTry.branch r11
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue checkpointBytes
    =>
    NMX_Actual02.t029 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError) residual

def t027 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) : Final := do
  let r10 ←
    (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
      verifier pool masterAccount
      master registryAccount entryAccount
      slot
  let cf9 ←
    core.result.Result.Insts.CoreOpsTry.branch r10
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_Actual02.t028 owners ops pool outputLane checkpointAccount laneAccount master masterKey
  | core.ops.control_flow.ControlFlow.Break residual
    =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError) residual

def t026 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) : Final := do
  if wrongMasterPda
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual02.t027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey

def t025 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) : Final := do
  let wrongMasterPda ←
    core.cmp.PartialEq.ne.trait_default
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      derivedMaster masterKey
  NMX_Actual02.t026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda

def t024 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) : Final := do
  let r8 ←
    ops.op38 masterSeeds
      pool
  let r9 ←
    core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r8 ()
  let cf8 ←
    core.result.Result.Insts.CoreOpsTry.branch r9
  match cf8 with
  | core.ops.control_flow.ControlFlow.Continue derivedMaster =>
    NMX_Actual02.t025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError) residual

def t023 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) : Final := do
  let mintSeed ←
    ops.op40
      mintKey
  let bumpSeed ←
    lift (Array.to_slice
      (Array.make 1#usize [ master.bump ]))
  let masterSeeds ←
    lift (Array.to_slice
      (Array.make 3#usize [
        r1_pool_adapter.PAIR_FOREST_MASTER_SEED, mintSeed, bumpSeed
        ]))
  NMX_Actual02.t024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds

def t022 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) : Final := do
  let mintKey ←
    ops.op37
      master.identity.asset_mint
  NMX_Actual02.t023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey

def t021 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) : Final := do
  if master.initialized_lane_mask != allLanes
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual02.t022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
end NMX_Actual02
end
