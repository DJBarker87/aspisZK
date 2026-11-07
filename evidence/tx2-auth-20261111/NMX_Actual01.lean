import NMX_ResultSteps
import NMX_Actual02
set_option autoImplicit false
noncomputable section
namespace NMX_Actual01
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

def t020 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) : Final := do
  let allLanes ←
    ops.op16
  NMX_Actual02.t021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes

def t019 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) : Final := do
  if wrongMaster
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_Actual01.t020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey

def t018 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) : Final := do
  let wrongMaster ←
    core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8 master.identity.pool masterKeyBytes
  NMX_Actual01.t019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster

def t017 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) (masterKey : solana_pubkey.Pubkey) : Final := do
  let masterKeyBytes ← ops.op39 masterKey
  NMX_Actual01.t018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes

def t016 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Master) : Final := do
  let masterKey ←
    r1_pool_adapter.owned.OwnedAccount.impl.key
      masterAccount
  NMX_Actual01.t017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey

def t015 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) : Final := do
  let r7 ← ops.op48 masterBytes
  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
  match cf7 with
  | core.ops.control_flow.ControlFlow.Continue master =>
    NMX_Actual01.t016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame solana_program_error.ProgramError)
      residual

def t014 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Final := do
  let r6 ←
    (r1_pool_adapter.owned.OwnedAccount.data ops) masterAccount
  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue masterBytes =>
    NMX_Actual01.t015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame solana_program_error.ProgramError)
      residual

def t013 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final := do
  let r5 ←
    (r1_pool_adapter.owned.require_distinct_accounts ops)
      (Array.make 7#usize [
        proof, masterAccount, checkpointAccount,
        laneAccount, registryAccount, entryAccount,
        verifierCheckpoint
        ])
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_Actual01.t014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame solana_program_error.ProgramError)
      residual

def t012 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final := do
  let r4 ←
    (r1_pool_adapter.owned.require_readonly_account ops) laneAccount
      pool
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_Actual01.t013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame solana_program_error.ProgramError)
      residual

def t011 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final := do
  let r3 ←
    (r1_pool_adapter.owned.require_readonly_account ops) checkpointAccount
      pool
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_Actual01.t012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
      solana_program_error.ProgramError) residual
end NMX_Actual01
end
