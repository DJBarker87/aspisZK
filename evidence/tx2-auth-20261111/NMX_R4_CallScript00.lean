import NMX_R4_CallProgram
import NMX_ResultSteps
import NMX_R4_CallScript01
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallScript00
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram

def t010 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let r2 ← child (.readonlyAccount masterAccount pool)
  let cf2 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r2)
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_R4_CallScript01.t011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth (core.convert.FromSame
      solana_program_error.ProgramError) residual)

def t009 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let r1 ← child (.checkpointGuard verifierCheckpoint verifier false)
  let cf1 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_R4_CallScript00.t010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth (core.convert.FromSame
      solana_program_error.ProgramError) residual)

def t008 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let r ← child (.readonlyBuffer proof)
  let cf ← scalar (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    NMX_R4_CallScript00.t009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Auth (core.convert.FromSame
      solana_program_error.ProgramError) residual)

def t007 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let verifierCheckpoint ← scalar (Slice.index_usize accounts 6#usize)
  NMX_R4_CallScript00.t008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint

def t006 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let entryAccount ← scalar (Slice.index_usize accounts 5#usize)
  NMX_R4_CallScript00.t007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount

def t005 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let registryAccount ← scalar (Slice.index_usize accounts 4#usize)
  NMX_R4_CallScript00.t006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount

def t004 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let laneAccount ← scalar (Slice.index_usize accounts 3#usize)
  NMX_R4_CallScript00.t005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount

def t003 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let checkpointAccount ← scalar (Slice.index_usize accounts 2#usize)
  NMX_R4_CallScript00.t004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount

def t002 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) : Program (core.result.Result Auth PE) := do
  let masterAccount ← scalar (Slice.index_usize accounts 1#usize)
  NMX_R4_CallScript00.t003 owners ops verifier accounts pool outputLane slot proof masterAccount

def t001 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) : Program (core.result.Result Auth PE) := do
  let proof ← scalar (Slice.index_usize accounts 0#usize)
  NMX_R4_CallScript00.t002 owners ops verifier accounts pool outputLane slot proof
end NMX_R4_CallScript00
end
