import S6CurrentAdapterModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result AdapterRw
namespace AspisS6CurrentBoxedDecoderSource

/-- The sole original child of the extracted thin boxed decoder. -/
structure Ops where
  decode : Slice U8 → Result (core.result.Result
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)

def decode_public_statement_box.closure := Unit

def decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once (ops : Ops)
  (c : decode_public_statement_box.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData


@[reducible]
def decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError (ops : Ops)
  : core.ops.function.FnOnce decode_public_statement_box.closure
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    (decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once ops)
}


def decode_public_statement_box (ops : Ops)
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    solana_program_error.ProgramError)
  := do
  let r ←
    ops.decode
      bytes
  let r1 ←
    core.result.Result.map_err
      (decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError ops)
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      (core.convert.FromSame solana_program_error.ProgramError) residual


#print axioms decode_public_statement_box
end AspisS6CurrentBoxedDecoderSource
