import NMX_OwnedPackets
import NMX_MasterValue
import NMX_CheckpointValue
set_option autoImplicit false
noncomputable section
namespace NMX_R4_BoxEmitted
open Aeneas Aeneas.Std Result AdapterRw
abbrev master.closure := Unit
abbrev checkpoint.closure := Unit
def
  master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
  (c : master.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData


@[reducible]
def
  master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
  : core.ops.function.FnOnce master.closure
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
}


def master (rawMaster : Slice U8 → Result (core.result.Result NMX_OwnedPackets.Master NJQ_Carrier.CF))
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
    solana_program_error.ProgramError)
  := do
  let r ←
    rawMaster
      bytes
  let r1 ←
    core.result.Result.map_err
      master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
      (core.convert.FromSame solana_program_error.ProgramError) residual


def
  checkpoint.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
  (c : checkpoint.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData


@[reducible]
def
  checkpoint.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
  : core.ops.function.FnOnce checkpoint.closure
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    checkpoint.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
}


def checkpoint (rawCheckpoint : Slice U8 → Result (core.result.Result NMX_OwnedPackets.Checkpoint NJQ_Carrier.CF))
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
    solana_program_error.ProgramError)
  := do
  let r ←
    rawCheckpoint
      bytes
  let r1 ←
    core.result.Result.map_err
      checkpoint.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
      (core.convert.FromSame solana_program_error.ProgramError) residual


end NMX_R4_BoxEmitted
end
