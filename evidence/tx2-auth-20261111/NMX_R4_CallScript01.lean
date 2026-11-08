import NMX_R4_CallProgram
import NMX_ResultSteps
import NMX_R4_CallScript02
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallScript01
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram

def t020 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let allLanes ← scalar (ops.op16)
  NMX_R4_CallScript02.t021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes

def t019 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) : Program (core.result.Result Auth PE) := do
  if wrongMaster
  then
    Program.ret (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NMX_R4_CallScript01.t020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey

def t018 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) : Program (core.result.Result Auth PE) := do
  let wrongMaster ← scalar (core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8 master.payload.identity.pool masterKeyBytes)
  NMX_R4_CallScript01.t019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster

def t017 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program (core.result.Result Auth PE) := do
  let masterKeyBytes ← scalar (ops.op39 masterKey)
  NMX_R4_CallScript01.t018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes

def t016 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) : Program (core.result.Result Auth PE) := do
  let masterKey ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key
      masterAccount)
  NMX_R4_CallScript01.t017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey

def t015 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) : Program (core.result.Result Auth PE) := do
  let r7 ← child (.master masterBytes)
  let cf7 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r7)
  match cf7 with
  | core.ops.control_flow.ControlFlow.Continue master =>
    NMX_R4_CallScript01.t016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame solana_program_error.ProgramError)
      residual)

def t014 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let r6 ← child (.data masterAccount)
  let cf6 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r6)
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue masterBytes =>
    NMX_R4_CallScript01.t015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame solana_program_error.ProgramError)
      residual)

def t013 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let r5 ← child (.distinct (Array.make 7#usize [proof,masterAccount,checkpointAccount,
  laneAccount,registryAccount,entryAccount,verifierCheckpoint]))
  let cf5 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r5)
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_R4_CallScript01.t014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame solana_program_error.ProgramError)
      residual)

def t012 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let r4 ← child (.readonlyAccount laneAccount pool)
  let cf4 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r4)
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_R4_CallScript01.t013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth
      (core.convert.FromSame solana_program_error.ProgramError)
      residual)

def t011 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let r3 ← child (.readonlyAccount checkpointAccount pool)
  let cf3 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r3)
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_R4_CallScript01.t012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth (core.convert.FromSame
      solana_program_error.ProgramError) residual)
end NMX_R4_CallScript01
end
